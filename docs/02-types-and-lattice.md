# Types and the lattice

A type checker needs a language for describing what a Ruby expression might
evaluate to. Typey's language is implemented by `Type` in `src/types.rs`.
Understanding it is the key to understanding almost every inference result.

## A type is a set of possible runtime values

The simplest interpretation is set-based:

- `String` means values that are strings.
- `Integer | nil` means an integer or `nil`.
- `T.noreturn` means the expression produces no normal value.
- `T.untyped` means the checker has deliberately lost static information.

Ruby is dynamic, so the checker often knows a set of possibilities rather
than one exact class. A union represents that set:

    value = if enabled
      "on"
    else
      0
    end
    # String | Integer

## The main Type variants

Typey represents:

| Variant | Example | Purpose |
| --- | --- | --- |
| `Any` | `T.untyped` | Gradual escape hatch; operations are accepted with little checking. |
| `Anything` | `T.anything` | Top-like value used by Sorbet's type-level operations. |
| `Never` | `T.noreturn` | An expression that cannot complete normally. |
| `Nil`, `True`, `False` | `nil`, `true`, `false` | Literal and flow-sensitive values. |
| primitives | `Integer`, `Float`, `String`, `Symbol` | Common Ruby value types. |
| `Object` | `Object` | Nominal root object type. |
| `Named` | `Array[String]`, `User` | Classes/modules and generic instantiations. |
| `Array`, `Hash`, `Tuple` | `Array[Integer]`, `{String => Integer}` | Structural collection information. |
| `Proc`, `BoundProc` | `(String) -> Integer` | Callable values and bound blocks. |
| `Union` | `String | nil` | Alternative possible types. |
| `Intersection` | `A & B` | A value satisfying multiple constraints. |
| `TypeVar` | `U` | A generic variable before substitution. |
| attached types | `T.attached_class`, `T.self_type` | Class-sensitive return types. |

The display syntax is intentionally close to Sorbet/RBS syntax, but display
is not the implementation. For example, an array may be represented
structurally with an element type while a named generic array may retain its
nominal name and arguments.

## Any, Anything, and Never are different

These three are easy to conflate.

### T.untyped (Any)

`T.untyped` means the checker does not know enough to check ordinary
operations. A call on it is usually accepted and returns a gradual result.
Sources include an explicit untyped annotation, `T.unsafe`, a declared
untyped signature, or a genuinely unresolved fallback.

`T.untyped` is not a convenient spelling for “I have not implemented this
method yet.” Replacing a provable `String` with `T.untyped` hides errors and
reduces coverage.

### T.anything (Anything)

`T.anything` is a type-level top used by Sorbet's type operations. It should
not automatically make every runtime call gradual. Preserving the distinction
lets joins and `T.must` behave differently from an explicitly untyped value.

### T.noreturn (Never)

`T.noreturn` describes an expression that raises, exits, or otherwise cannot
produce a normal value:

    def fail_with_message
      raise "stop"
    end

`Never` is removed from an ordinary union because it contributes no normal
value. But it must remain visible in control-flow metadata so code after a
terminating expression is not treated as if it were reached normally.

## Join: the least common safe summary

The join operation, written conceptually as `A | B`, answers:

> What type safely describes a value that may be an A or a B?

Examples:

    join(String, nil)       = String | nil
    join(Integer, Integer)  = Integer
    join(Never, String)     = String
    join(Array[String], Array[Integer])
                            = Array[String | Integer]

Unions are flattened and normalized. Duplicate alternatives are removed.
Structural arrays, hashes, tuples, and procs can be joined recursively when
their shapes are compatible.

Joining is the main reason fixpoint inference terminates: summaries become
more inclusive as more call paths are discovered, and a stable union is
eventually reached.

## Meet: the intersection of a path and a fact

The meet operation answers:

> What values satisfy both the current type and this new constraint?

It is used for flow-sensitive narrowing:

    def print_name(value)
      return unless value.is_a?(String)
      value.length
    end

On the branch after the predicate, the current type is met with `String`.
If the current type was `String | nil`, the result is `String`. If the types
are disjoint, the path can be unreachable.

`Any` and `Anything` require special treatment: they represent lack of
knowledge rather than ordinary nominal sets. A meet must not accidentally
turn uncertainty into a false proof.

## Removing possibilities

`without(A, B)` removes values described by `B` from `A`. It powers negative
branches:

    if value.nil?
      # value is nil
    else
      # value is value_type without nil
    end

For union types, removal is structural. Removing `nil` from
`String | Integer | nil` leaves `String | Integer`. Removing an entire
discriminant can make a path `Never`.

## Truthiness is not the same as non-nilability

Ruby treats only `false` and `nil` as falsey. A value of type `Integer | nil`
is truthy on the `Integer` branch, but an `Object` may still be either false
or nil at runtime unless the type system has a stronger fact.

Typey exposes truthy and falsey portions and uses them in `if`, `unless`,
`while`, and logical operators. Do not implement “not false” by merely
removing `nil` everywhere: a branch can prove truthiness without proving a
database field is non-null or a receiver has a particular object state.

## Subtyping

Subtyping answers whether every value in one type is safe where another type
is expected:

    Integer <: Object
    String <: Object
    String <: String | nil
    String | nil </: String

Unions are covariant for the purpose of checking membership: each alternative
must fit the target. Generic containers and procs need variance-aware rules;
argument positions are generally contravariant while return positions are
covariant. When a rule is not implemented, do not “fix” the result by
returning `T.untyped`; add the missing relation or preserve the uncertainty.

## Containers, tuples, and calls

An `Array[U]` tells us what a normal element read returns. A tuple keeps
position-specific information:

    pair = ["name", 3]
    pair[0] # String
    pair[1] # Integer

A method such as `map` transforms the element type according to its block. A
method such as `select` preserves the element type while narrowing the block
input. Methods that change shape, such as `to_h`, `zip`, or splat replacement,
need dedicated generic reasoning when the ordinary signature alone cannot
express the result.

## Generic variables

Type variables are placeholders, not user-facing answers:

    def identity[U](value)
      value
    end
    # A signature can state that the result is U.
    identity("x") # String

The call binds `U` from the actual argument and substitutes it into the
return type. An unresolved `U` must not leak into a final inferred type. If
there is no evidence, the checker may use a gradual fallback; if there is
evidence, it should preserve the concrete type.

## Attached and self types

`T.attached_class` means “the class object associated with the receiver,” not
just the base class `Class`. A constructor-style method on a subclass should
return the subclass:

    class Base
      extend T::Sig
      sig { returns(T.attached_class) }
      def self.build
        new
      end
    end

    class Child < Base; end
    Child.build # Child

`T.self_type` similarly preserves the receiver's precise type in fluent APIs.
These types must be substituted during receiver-aware dispatch rather than
special-cased to `Object` or `Class`.

## Adding precision safely

When a result is too broad, ask in order:

1. Is the declaration missing?
2. Is the call resolving to the wrong owner or singleton/instance side?
3. Is a type variable not being substituted?
4. Is a flow fact being dropped at a join or mutation?
5. Is a collection operation changing shape?
6. Is the value genuinely unknown?

Only the last answer justifies `T.untyped`. The type lattice should carry
uncertainty explicitly while retaining all concrete evidence it has.
