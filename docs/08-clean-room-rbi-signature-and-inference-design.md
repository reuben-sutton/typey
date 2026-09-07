# Clean-room design: RBIs, signatures, RBS comments, and inference

This document specifies the part of Typey that turns Ruby source, Sorbet
signatures, RBS comments, and RBI declarations into checked and inferred
types. It is written so that an independent implementation can reproduce the
observable behavior without sharing Typey's source code.

The compatibility target is Sorbet's observable behavior where that behavior
is intentional. The precision rule is stronger than “make the same number of
diagnostics”: if the available program and declaration information proves a
concrete type, retain it. In particular, `T.untyped` is not a placeholder for
an unimplemented checker feature.

## 1. Contract and vocabulary

The implementation answers three separate questions:

1. Which declarations exist?
2. What values can an expression produce?
3. Is the operation valid for those values?

Registration answers the first question. Inference answers the second. The
diagnostic layer answers the third. Keeping these layers separate is
essential. A missing RBI method is normally a declaration problem; changing
the result to `T.untyped` would hide the problem rather than solve it.

The terms below have precise meanings in this design:

* **Source** is a `.rb` implementation file. Its method bodies are analyzed.
* **RBI** is a `.rbi` declaration file. It can declare classes, methods,
  constants, ancestors, and signatures for code whose implementation is
  absent or intentionally external.
* **Built-in RBI** is the vendored Sorbet collection for Ruby and the standard
  library. It is a baseline input, not application source.
* **Project RBI** is any repository or gem RBI, including generated RBIs such
  as Tapioca output. It is an input contract and must not be rewritten merely
  to silence a finding.
* **Signature** is a method contract from Sorbet `sig` syntax or an RBS
  comment. A signature is attached to a declaration, not treated as an
  arbitrary runtime expression.
* **Summary** is the inferred contract of an unsigiled method: parameter
  types, keyword and block shape, return type, and termination behavior.
* **Concrete** means a type that contains no `T.untyped` (`Any`) at any
  nesting depth. A union or generic type can still be concrete.
* **Unknown** means the checker has insufficient evidence. Unknown is allowed
  to remain gradual; it must not be confused with a proven `T.untyped` or
  with `T.noreturn`.

The implementation must never edit application Ruby to make an analysis pass.
When a finding is wrong, reduce it to a fixture and fix the parser, declaration
model, type operation, flow rule, or inference dependency that caused it.

## 2. End-to-end architecture

The complete pipeline is:

```text
filesystem
   │
   ├─ discover .rb/.rbi files, apply sorbet/config and CLI ignores
   ├─ read file-level # typed: modes
   └─ load built-in RBI baseline
   │
   ▼
Prism AST + source/comment annotation records
   │
   ├─ source ranges and file-origin metadata
   ├─ Sorbet sig records
   └─ RBS comment records and inline assertions
   │
   ▼
declaration registration
   │
   ├─ method states and signatures
   ├─ classes, modules, ancestors, aliases, accessors
   ├─ constants, ivars, generic members, struct fields
   └─ source/RBI precedence and lexical type-name resolution
   │
   ▼
seed evaluation ──► dependency graph and initial method/shared summaries
   │
   ▼
changed-summary worklist ──► fixed point
   │
   ▼
final reporting traversal
   │
   ├─ diagnostics
   ├─ per-expression types
   └─ send/untype coverage metrics
```

Ruby syntax is parsed with Prism (or an equivalent Ruby parser with exact
source spans). The checker must not execute the Ruby process to discover
signatures or declarations: arbitrary metaprogramming is not a sound source of
static facts.

For a repository check, concatenate files into one logical program after
recording each file's byte range. Insert a syntactically valid, non-comment
boundary between files so a pending RBS comment cannot attach to a declaration
in the next file. After analysis, map every diagnostic and inferred type back
through the recorded ranges. A single workspace is required so a method in a
project RBI can type a call in a source file.

## 3. File discovery and policy

### 3.1 Files in the workspace

Directory discovery includes files whose extension is exactly `.rb` or `.rbi`.
Results are sorted and deduplicated for deterministic behavior. The default
walker skips repository metadata and generated/upstream checkouts:

* `.git`
* `target`
* `node_modules`
* local upstream checkouts used only for conformance, such as
  `sorbet-upstream` and `spinel-upstream`

The repository's `sorbet/config` is read for `--ignore PATTERN` and
`--ignore=PATTERN`. Command-line ignore patterns are added to the same set.
An anchored pattern matches from the repository-relative path; an unanchored
pattern matches a path component or substring. Ignore filtering occurs before
file loading, so ignored files contribute no declarations and no diagnostics.

The built-in baseline is loaded from Typey's vendored Sorbet RBI tree. It is
added to the workspace after project discovery and tagged separately from
project RBIs. A library API should also allow callers to supply an explicit
file order when load-order approximation matters.

### 3.2 File-level `typed:` modes

Scan the leading comment area (the first twenty lines) for the first valid
Sorbet sigil:

| Sigil | Declaration registration | Body checking | Extra requirement |
| --- | --- | --- | --- |
| `typed: ignore` | skip file | skip file | none |
| `typed: false` | retain enough syntax/declaration data for workspace integrity | suppress ordinary type diagnostics | preserve parse diagnostics |
| `typed: true` | normal | report unsafe or missing API operations | no complete-summary requirement |
| `typed: strict` | normal | report as above | every source method needs sufficient inferred information |
| `typed: strong` | normal | strict behavior plus stronger policy hooks | implementation may add strong-mode checks |
| no sigil | normal | treat as `typed: true` | deliberate Typey measurement policy |

The sigil scanner is line-based so text inside a string or heredoc is not a
directive. `typed: false` and `typed: ignore` are policy decisions, not
permission to turn expressions into `T.untyped`. An explicit signature or
parse error remains meaningful even when ordinary body diagnostics are
suppressed.

Store strictness as source ranges in the combined workspace. A diagnostic or
inference-gap check asks which range contains its source offset rather than
assuming the entire concatenated program has one mode.

## 4. The type representation

The minimum type algebra is:

| Internal form | Sorbet-like spelling | Meaning |
| --- | --- | --- |
| `Any` | `T.untyped` | gradual escape hatch; ordinary operations are not statically checked |
| `Anything` | `T.anything` | type-level top-like value; do not treat it as ordinary dynamic data |
| `Never` | `T.noreturn` / `bot` | no normal value is produced |
| `Nil`, `True`, `False` | `nil`, `true`, `false` | literal facts useful for flow |
| primitive forms | `Integer`, `Float`, `String`, `Symbol` | built-in value types |
| `Object` | `Object` | nominal root |
| `Named(name, args)` | `User`, `Array[String]` | nominal class/module, optionally generic |
| `Array(element)` | `Array[T]` | homogeneous array shape |
| `Hash(key, value)` | `Hash[K, V]` | key/value shape |
| `Tuple(elements)` | `[A, B]` | fixed length and position types |
| `Proc(params, result)` | `(A) -> B` | callable type |
| `BoundProc(receiver, params, result)` | `T.proc.bind(...)` | callable type with a static block `self` |
| `Union(members)` | `A | B` | alternative values |
| `Intersection(members)` | `A & B` | simultaneous constraints |
| `TypeVar(name)` | `T.type_parameter(:U)` / `U` | unresolved generic variable |
| `AttachedClass` | `T.attached_class` | class object’s late-bound instance type |
| `AttachedClassOf(owner)` | internal attached-class context | attached type while checking an owner’s body |

### 4.1 Algebraic invariants

Constructors canonicalize types:

* flatten nested unions and intersections;
* remove duplicate members;
* remove `Never` from unions;
* collapse compatible container shapes recursively;
* preserve nilability instead of allowing a broad nominal type to erase a
  separately observed `nil` member;
* sort members deterministically for stable diagnostics and fixtures.

`join(a, b)` is the least upper bound used when paths or observations merge.
Examples:

```text
join(String, nil)                 = String | nil
join(Integer, Integer)             = Integer
join(Never, String)                = String
join(Array[String], Array[Integer])= Array[String | Integer]
```

`meet(a, b)` is the greatest lower bound used for path refinement. A meet with
`Never` is `Never`; a union is refined member-by-member; definitely disjoint
primitive types meet to `Never`. `without(value, excluded)` removes excluded
union members and powers negative predicates.

`is_subtype_of` must distinguish gradual consistency from proof. `Any` is
compatible with every expected type for ordinary checking, but a result that
contains `Any` must remain marked as gradual. `Anything` is not a reason to
accept every runtime method call. `Never` is a subtype of every type because
it has no normal inhabitants.

Do not use `Any` as an internal “not visited yet” marker in a way that can
escape. Keep unresolved method slots as `Option<Type>` or a separate
provisional state. A provisional recursive call may use `Never` to avoid
poisoning a caller before an external call supplies evidence; an external RBI
declaration without a body should use gradual `Any`, not `Never`.

### 4.2 Truthiness and nilability

Ruby falsey values are exactly `nil` and `false`. Define:

```text
truthy_part(T)  = T without (nil | false)
falsy_part(T)   = the nil/false members of T
```

Truthiness does not prove every property of an object. It can remove nil from
the local expression on a guarded path, but it must not globally change the
class of an Active Record object or claim a nullable database column is
non-null. Object-state facts such as persisted/new/destroyed are separate
from nominal type and must be joined and invalidated independently.

## 5. Declaration and signature IR

### 5.1 Method identity

Every declaration has a stable key:

```text
MethodKey = (owner: optional qualified name, name, singleton: boolean)

User#name  -> (User, "name", false)
User.find  -> (User, "find", true)
top-level  -> (none, "helper", false)
```

The singleton bit is mandatory. A class object and an instance can both expose
`new`, `name`, or `call`, but they are different dispatch domains.

### 5.2 Method signatures

The signature IR contains:

```text
MethodSig {
  positional_types: [Type]
  parameter_kinds: [positional | optional | rest | keyword | optional_keyword |
                    rest_keyword | block]
  parameter_names: [String]       # Sorbet param names when available
  required_positional: Integer
  rest_index: optional Integer
  keywords: Map[String, {type: Type, required: Boolean}]
  accepts_keyword_rest: Boolean
  type_parameters: [String]
  block: optional Proc or BoundProc, possibly nilable
  return_type: Type
  is_void: Boolean
  is_abstract: Boolean
}
```

Keep the original overload list as well as a merged fallback signature. The
merged signature is useful for registration and recursive summaries; overload
selection should first choose a contract whose arity, keyword shape, block
presence, and known argument types accept the call. If no overload matches,
use the merged contract for diagnostics so a dynamic splat can still be
checked conservatively.

### 5.3 Inferred method state

An unsigiled source method has an evolving state:

```text
MethodState {
  parameter_types: [optional Type]
  rest_index: optional Integer
  keyword_types: Map[String, optional Type]
  required_keywords: Set[String]
  yield_parameter_types: [optional Type]
  block_return_type: optional Type
  block_contract: optional Proc
  accepts_rest: Boolean
  accepts_keyword_rest: Boolean
  required_positional: Integer
  return_type: optional Type
  return_terminates: Boolean
  explicit: Boolean
  overloads: [MethodSig]
  visibility: public | protected | private
}
```

`explicit` means that a source signature, project RBI, built-in RBI, or
generated explicit contract owns the state. Inference may check an explicit
body but must not widen its declared return simply because the implementation
currently disagrees.

### 5.4 Classes and shared facts

For each class/module keep:

```text
ClassInfo {
  is_module: Boolean
  superclass: optional qualified name
  includes: [qualified name]
  prepends: [qualified name]
  extends: [qualified name]
  required_ancestors: [qualified name]
  extend_self: Boolean
  class_methods: [qualified name]
  generic_members: Map[name, {index, fixed_type?}]
  attached_class_member: optional index
  struct_fields: optional [name]
}
```

Shared inference facts are keyed separately so dependency invalidation can be
precise:

```text
Ivar(owner, singleton, name)
Constant(qualified_name)
ClassVar(owner, name)
Global(name)
StructField(owner, name)
```

An accessor declaration records whether it is a reader or writer. If no
annotation exists, a reader may obtain its type from the corresponding ivar
summary; a writer observes its argument and updates that shared fact. An
explicit accessor annotation takes precedence over an inferred ivar type.

## 6. Collecting Sorbet signatures

### 6.1 Pair signatures with real AST declarations

First parse the whole Ruby buffer with Prism and collect offsets for:

* `def` and singleton `def` nodes;
* class and module declarations;
* `sig` call nodes whose receiver is absent;
* `attr_reader`, `attr_writer`, and `attr_accessor` call nodes.

Then associate annotations by source offset, not by method name alone. A name
map is unsound when two owners define `initialize`, `remove`, or `call`.
Only trivia and allowed method modifiers may occur between a `sig` call and its
definition. This prevents a signature in a heredoc, string, nested method, or
unrelated statement from leaking to the next declaration.

Consecutive `sig` calls immediately before one definition form overloads in
source order. The same association rule applies to an attribute macro.

### 6.2 Parse the supported Sorbet contract

Parse the recognized call structure without executing it:

```ruby
sig do
  type_parameters(:U)
    .params(value: T.type_parameter(:U))
    .returns(T.type_parameter(:U))
end
```

The parser extracts:

* `type_parameters(:U, :V)` into the method’s type-parameter list;
* `.params(name: Type, other: Type)` into named parameter slots;
* `.returns(Type)` into the result contract;
* `.void` into `return_type = nil` plus `is_void = true`;
* `.abstract` or `abstract` into `is_abstract = true`;
* nested `T.*` expressions into the type algebra.

If a signature has parameter or return syntax but no parseable return, the
contract is not silently discarded. Preserve a signature diagnostic or an
explicit gradual type according to the syntax being parsed.

The parser must support at least:

```text
T.untyped                  -> Any
T.anything                 -> Anything
T.noreturn / bot           -> Never
T.nilable(A)               -> Nil | A
T.any(A, B)                -> A | B
T.all(A, B)                -> A & B
T.class_of(A)              -> Class[A]
T.attached_class           -> AttachedClass
T.self_type                -> receiver-instance sentinel
T.type_parameter(:U)       -> TypeVar("U")
T.proc.params(...).returns(A)
T.proc.bind(Receiver) ...  -> BoundProc
Array[A], Hash[K, V]
```

`T.self_type` is not `Object` and `T.attached_class` is not merely `Class`.
They are substituted at dispatch time. A class-level method inherited by
`Child` must return `Child` when its contract says `T.attached_class`.

### 6.3 Reconcile Sorbet parameter names with Ruby shape

Ruby’s Prism parameter list is authoritative for whether a parameter is
positional, keyword, rest, or block. Sorbet’s `params` names supply types. Map
them in this order:

1. Match ordinary names to Ruby positional or keyword names.
2. Treat Sorbet’s special name `"&"` as the Ruby block slot, even when the
   source block parameter is named `&block`.
3. Match a named proc contract to the actual block name when both are present.
4. Preserve `nilable(Proc)` for an optional `&block`; it is different from a
   required block.
5. Preserve Ruby rest/keyword-rest shape even if the signature omits a name.

For source signatures, report unknown parameter names and malformed block
parameter declarations. Do not apply those source-shape diagnostics to RBI
declarations that intentionally describe an external method.

### 6.4 Signature semantics

* `void` is a contract/effect. Calls produce `nil`; the implementation’s last
  expression is not treated as the declared return value.
* `abstract` describes an interface. Do not require an absent implementation
  body to satisfy the contract.
* An explicit return contract is checked against every normal return path and
  against implicit method fallthrough where applicable.
* `T.cast(value, A)` checks or records the asserted target and returns `A`.
* `T.must(value)` removes `nil` from the expression and reports if the value
  is definitely nil.
* `T.unsafe(value)` intentionally returns `Any` and marks the origin as
  `Unsafe`.
* `T.let(value, A)` checks the value against `A` and returns `A`.
* `T.absurd(value)` requires an impossible/empty path and returns `Never`.
* `T.reveal_type(value)` records a note but should not alter the value’s type.

## 7. Collecting RBS comments

RBS comments are always enabled in this design; they are not gated by a
Sorbet DSL module being required.

### 7.1 Lexical comment scanner plus AST anchoring

Scan lines to form pending records, then use the Prism AST to attach them to
real declarations. A pending RBS record starts with `#:` and may continue on
following `#|` lines. Blank lines and ordinary comments may separate it from
the declaration. A non-comment Ruby statement clears it.

The pending record attaches to the next real node on the same lexical track:

* `def` or singleton `def` → method signature;
* `class` → class-level type parameters such as `[Elem < Object]`;
* `attr_reader`/writer/accessor → generated method signature;
* a standalone type expression after an assignment → inline assertion.

Do not attach text that merely resembles a comment inside a string or heredoc.
Do not attach a comment from one concatenated workspace file across the
synthetic file boundary.

### 7.2 Method signature grammar

The implementation needs the following RBS subset:

```text
[T, U] (A, ?B, *C, key: D, ?optional: E, **F) { (X) -> Y } -> Z
```

Rules:

* a leading `[T, U]` declares method type variables; bounds and variance may
  be parsed and retained even if the first implementation only uses names;
* ordinary entries are positional parameters;
* `?A` in a parameter position means the argument may be omitted, not that its
  value is nilable;
* `*A` is a variadic positional parameter;
* `key: A` and `?key: A` are required and optional keywords;
* `**A` accepts additional keywords;
* `{ (X) -> Y }` is a required block and `?{ (X) -> Y }` is optional;
* the right side of `->` is the return type;
* `void` maps to the nil/effect contract;
* `A?` in a type expression means `nil | A`;
* `A | B`, `A & B`, tuples `[A, B]`, arrays, hashes, named generics,
  `T.proc`, and inline records are recursively parsed.

Keep optional argument shape separate from nilability. For example, an
omittable `?suffix: String` is not equivalent to a required `suffix: String?`.

### 7.3 Type aliases and attributes

`#: type Name = Type` declares an alias in the current lexical namespace. Keep
the alias unresolved until registration has enough class/module names to
resolve short references.

An attribute can use either:

```ruby
#: () -> String
attr_reader :name
```

or a short form:

```ruby
#: String
attr_reader :name
```

The short form is the reader result. For a writer, transform it into one
required parameter of that type and a nil/void result. For `attr_accessor`,
apply the reader contract to the reader and the transformed contract to the
writer. If no annotation exists, use the ivar fact when available.

### 7.4 Trailing assertions

RBS-style trailing assertions are expression facts, not method declarations:

```ruby
value = expression #: String
value = expression #: as String
value = expression #: as !nil
expression #: absurd
expression #: self as SomeHost
```

`as A` is a cast-like assertion, `as !nil` is a must-like refinement,
`absurd` asserts an impossible path, and `self as A` narrows the receiver for
the following expression. Apply an assertion only to its source expression;
do not mutate the global nominal type of the surrounding object.

### 7.5 Malformed comments

Malformed signatures must be diagnosed at their comment/declaration location
or retained as a clearly gradual contract. They must not disappear silently.
In particular, malformed block signatures and malformed `T.proc` contracts
are useful compatibility tests because a dropped block type changes later
argument and yield checking.

## 8. RBI loading and precedence

### 8.1 Declaration source order is not semantic precedence

Files may be loaded in deterministic path order, but contract precedence is
explicit. For a given `MethodKey`, use:

```text
source sig for the method
    > project/gem RBI sig
    > built-in RBI sig
    > inferred source body summary
    > unresolved/gradual fallback
```

The source implementation can receive a project RBI contract when the source
method has no local signature. A local source signature wins when both exist.
An external RBI method has no body to infer, so its signature remains the
contract. A declaration with no signature is still a declaration; it is not
the same as an absent method.

If multiple signatures have the same priority, retain all as overloads and
build a merged fallback. Do not let a broad built-in declaration overwrite a
more precise project declaration. Do not let a project RBI rewrite a vendored
RBI file; the merge happens in the checker’s declaration tables.

### 8.2 RBI ranges and diagnostics

Record byte ranges for project RBI and built-in RBI files in the combined
workspace. Use those ranges to:

* classify a signature as source, project RBI, or built-in;
* suppress “missing API inside an RBI declaration” diagnostics;
* still type-check application calls against RBI contracts;
* map diagnostics back to the correct original file.

An RBI declaration with an explicit `T.untyped` return is a deliberate gradual
boundary and should be marked `DeclaredSignature`. An RBI declaration with no
body and no useful signature should use an external gradual return (`Any`) so
callers are not accidentally treated as unreachable. That fallback must remain
explainable in metrics.

## 9. Declaration registration

Registration happens for the entire workspace before any body inference.
Use a Prism visitor with these stacks:

* lexical class/module owners;
* singleton owners (`class << self`, `def self.x`, or explicit receiver);
* default visibility;
* method nesting depth, so class DSL calls are not mistaken for top-level
  declarations inside method bodies.

The visitor records source spans for every definition and its Ruby parameter
shape. Then it performs a second reconciliation step that attaches collected
signatures to those definition keys.

### 9.1 Classes, modules, and lookup

Register each class/module before visiting its body. Resolve qualified names
relative to the current lexical owner; an absolute `::Name` bypasses the
lexical prefix. Record superclass, includes, prepends, extends, required
ancestors, `extend self`, and `module_function` aliases.

For an instance receiver, search in this order:

1. prepended modules, from nearest to farthest;
2. the receiver’s own class;
3. required ancestors and included modules in Ruby lookup order;
4. the superclass chain.

For a class-object receiver, search singleton declarations first, then
extended modules and class-object behavior (`Class`/`Module`) as appropriate.
A union receiver is dispatched branch-by-branch and its result is joined. A
cycle in the ancestor graph terminates lookup with a visited-owner set.

Cache successful and unsuccessful resolution by `MethodKey`, and invalidate
the cache if registration changes the class graph.

### 9.2 Generated declarations

Registration must model declarations created by common static DSLs without
executing arbitrary Ruby:

* `attr_reader`, `attr_writer`, and `attr_accessor`;
* aliases, `alias_method`, and `module_function`;
* `T::Struct` `prop`/`const` fields;
* `Struct.new` subclasses and their generated field readers, writers, and
  initializer shape;
* known delegation declarations such as `delegate` when the target and
  generated name are statically visible;
* framework declarations supplied by project RBIs or narrow, reusable DSL
  adapters.

For `Parameter = Struct.new(:name) { ... }`, the assignment creates a named
class. Register the generated class and evaluate its block as that class body,
so methods declared inside the block have owner `Parameter`. This is a
general dynamic-class rule, not an application-specific method exception.

Do not model every arbitrary call as a declaration generator. If a DSL cannot
be recognized safely, preserve the unknown boundary and require an RBI or an
explicit adapter.

### 9.3 Generic and attached members

Register class-level type parameters and fixed members. A generic class value
such as `Box[String]` carries its arguments. A method referring to `Box::Elem`
resolves that member from the actual receiver’s generic arguments. If the
member is fixed, use the fixed type; if the receiver has no argument, retain
the open/gradual state rather than inventing a concrete type.

`has_attached_class!` registers the module’s attached member. Validate
`T.attached_class` usage at registration:

* class singleton methods may use it;
* module instance methods require `has_attached_class!`;
* module singleton methods cannot use it as an instantiable class;
* it may not be used in an input position where Sorbet requires an output
  context.

## 10. Inference state and flow

### 10.1 Environment

An evaluation environment contains:

```text
Environment {
  local_types: Map[name, Type]
  inferred_local_names: Set[name]
  provisional_local_names: Set[name]
  open_array_locals: Set[name]
  known_nonempty_arrays: Set[name]
  predicate_aliases: Map[name, predicate fact]
  known_truthiness: Map[name, true/false]
  self_type: Type
  current_method: optional MethodKey
}
```

Binding a local clears stale predicate, truthiness, and collection-shape facts.
Facts observed from calls to an unsigiled method may help expression inference,
but are marked provisional until the method summary has converged; one sample
call is not proof of every future call.

### 10.2 Evaluation result

Every AST evaluation returns both a type and control-flow information:

```text
Eval {
  all_values_type: Type
  normal_type: optional Type
  flow: bitset {normal, return, raise, break, next, retry}
  abrupt_types: {
    return: Type, raise: Type, break: Type,
    next: Type, retry: Type
  }
}
```

`normal_type` is absent when no path continues normally. `all_values_type` is
the join of normal and abrupt values for reporting, while method return
summaries use the appropriate normal/return outcome. `Never` represents an
empty outcome, not an unknown value.

For a sequence, evaluate left to right. Only normal paths continue to the next
expression; abrupt paths are carried separately. For a branch, evaluate both
paths, join normal result types, and join post-branch environments. A fact is
retained after a merge only if it holds on every normal path. Rescue and ensure
must preserve their distinct raise/retry/normal edges.

### 10.3 Narrowing and invalidation

Implement path refinements using `meet` and `without`:

* `if value` → `truthy_part(value)` in the then path;
* `unless value` → `falsy_part(value)` in the then path;
* `value.nil?` → `nil`/non-nil branches;
* `value.is_a?(A)` → meet with `A` on the positive branch;
* negative tests → remove the proven alternative;
* early `return`, `raise`, `break`, and `next` remove the corresponding path.

Any reassignment invalidates facts for that local. Calls known to mutate an
object invalidate object-state facts that the call can affect. A nominal class
fact and a typestate fact are different dimensions and must not be conflated.

## 11. Call inference

All ordinary sends, operator sends, `super`, `yield`, index operations, and
compound assignments pass through a common call path or an equivalent
structural model. The conceptual algorithm is:

```text
evaluate receiver (if any)
evaluate positional, keyword, splat, and forwarded arguments
evaluate/record the block expression
for each possible receiver type:
    resolve MethodKey through aliases and ancestor graph
    if explicit signature exists:
        choose matching overload or merged fallback
        infer type variables from arguments, block, and receiver generics
        substitute type variables, generic members, self_type, attached_class
        check arity, keyword shape, argument types, and block contract
        compute the declared return and termination
    else if a structural Ruby/Sorbet model applies:
        use the model’s receiver/argument relationship
    else if an inferred method summary exists:
        observe argument evidence and use its current return summary
    else:
        report missing API when policy requires it
        return a marked fallback/gradual result
join the results of all receiver branches
apply safe-navigation nilability and assignment semantics
record the send, dependencies, and untyped origin
```

The exact order between structural models and inferred method dispatch may be
optimized, but an explicit declaration always controls a declared method. A
model is justified when the relationship cannot be expressed by the available
signature alone, for example `Array#map`, `select`, `reduce`, `Hash#[]`, or
tuple-preserving operations.

### 11.1 Arguments and splats

Represent call arguments with:

* original AST nodes and source indices;
* positional types and keyword name/type pairs;
* known tuple splats;
* dynamic array splats and their element type;
* keyword splats, including whether their keys are known;
* forwarding `...`;
* block presence or `&expression`.

A tuple splat preserves arity and position. An ordinary `Array[T]` splat
represents zero or more `T` values and cannot prove a fixed arity. A dynamic or
forwarded splat may make overload selection permissive, but it must not erase
types already known for non-splat arguments.

### 11.2 Generic substitution

At a call site, bind `TypeVar` occurrences from actual arguments and block
results. For a signature

```ruby
sig do
  type_parameters(:U)
    .params(value: T.type_parameter(:U))
    .returns(T.type_parameter(:U))
end
```

`identity("x")` binds `U -> String`. Also bind open generic class members
from receiver arguments, for example a `Box[String]` receiver supplying
`Box::Elem = String`.

Substitute recursively through named generics, arrays, hashes, tuples, procs,
bound procs, unions, intersections, blocks, and returns. An unresolved type
variable must not leak into a user-facing inferred type. If no evidence exists,
use a documented gradual fallback; if evidence exists, preserve it.

### 11.3 Blocks and bound blocks

A block contract is a callable type. For a literal block:

1. obtain expected yield parameter types from the selected signature or
   inferred method state;
2. bind block parameters, including tuple destructuring;
3. set `self` to the receiver required by the operation;
4. evaluate the block body and infer its result;
5. check result type against the block return contract;
6. propagate `break`, `next`, and captured locals according to Ruby control
   flow.

`T.proc.bind(Receiver)` creates `BoundProc`; evaluate the block with that
receiver as `self`. A `Class.new(Base) { ... }` block uses the generated class
instance as its receiver. `define_method` binds its block to instances of the
receiving class. Optional blocks retain nilability and may be absent.

### 11.4 Fallback policy

If the receiver is explicitly `Any`, ordinary dynamic calls are accepted and
the result is gradual. If the receiver is concrete but the method is absent,
report the missing API in `typed: true` or stronger modes and retain a
`FallbackCall` origin for any fallback result. If the receiver is an unknown
class object or an unmodeled external boundary, record the missing contract so
the finding can be fixed by registration/RBI/model work.

Never replace a concrete known operation with `Any` merely because another
branch is unknown. Preserve concrete union members and use structural models
for known Ruby operations. For recursive inferred methods, use a finite,
documented widening point such as `Object` when necessary to avoid unbounded
nested types; do not use `Any` solely to force convergence.

## 12. Fixpoint inference

### 12.1 Phases

The analyzer runs these phases:

| Phase | Reports ordinary diagnostics? | Purpose |
| --- | --- | --- |
| registration | signature/declaration errors only | build all declaration and annotation tables |
| seed | no | traverse top-level code, observe calls, seed summaries and dependencies |
| worklist rounds | no | reevaluate changed methods/shared readers and commit summaries |
| final | yes | traverse with settled summaries, record types and diagnostics |

The seed pass evaluates top-level code and discovers calls into methods. For an
inferred method, observed argument types join into parameter slots and normal
returns join into the return slot. Explicit methods do not widen their
contracts.

### 12.2 Dependency graph

Maintain:

```text
method_callers[callee]       = methods whose result depends on callee
method_shared_reads[method]  = ivar/constant/class-var/global/field facts read
shared_readers[shared_fact]  = methods to reschedule when that fact changes
```

Each worklist evaluation reads summaries committed before the round. Candidate
returns and shared facts are committed synchronously after the traversal. If a
method’s return or parameter summary changes, schedule its callers and itself.
If a shared fact changes, schedule its readers. Resolution caches are
invalidated when class graph facts change.

Pseudocode:

```text
register_everything()
parse_errors = registration_diagnostics

report = false
seed_calls = true
evaluate_workspace_top_level()
commit_method_and_shared_changes()

pending = all_inferred_methods
while pending is not empty:
    active = pending
    clear candidate changes
    evaluate_workspace_with_only(active method bodies updating summaries)
    commit all candidates together
    pending = callers(changed methods)
              ∪ readers(changed shared facts)
              ∪ changed methods

report = true
evaluate_workspace_again()
append strict-mode inference gaps
deduplicate and sort diagnostics/types
```

There is no arbitrary maximum round count. If a run appears to revisit the
same methods indefinitely, inspect the summary equality, union normalization,
dependency edges, or invalidation breadth. A lower round limit hides a bug and
can produce fewer diagnostics by stopping before a real call is analyzed.

### 12.3 Summary convergence

Summaries move monotonically toward a stable result under the type join. A
summary comparison must include:

* each positional and keyword slot;
* rest and block shape;
* return type;
* whether all normal returns terminate;
* shared facts observed by the method when they affect callers.

Do not compare only the return type: doing so can leave a callee’s parameter
or block contract stale while callers appear converged.

For a direct recursive call, do not feed a provisional `Any` parameter back
into itself. Use the current committed summary or a finite widening rule, then
allow external concrete calls to refine the method in later scheduling.

## 13. Diagnostics and observable results

### 13.1 Diagnostic classes

At minimum, distinguish:

* Prism parse errors;
* malformed Sorbet/RBS signature errors;
* unknown or mismatched parameter shapes;
* argument, keyword, block, assignment, and return mismatches;
* missing methods or constants on concrete receivers;
* invalid `T.attached_class` usage;
* unreachable/absurd-path diagnostics;
* strict/strong methods with incomplete inferred summaries.

Diagnostics carry severity, message, and byte start/end. Deduplicate by
severity, span, and message after the final pass, then sort by source offset and
message for deterministic output.

### 13.2 Type records and untyped origins

For each recorded expression, expose:

```text
InferredType {
  start, end: byte offsets
  type: Type
  untyped_origin: optional ExplicitAnnotation | Unsafe | DeclaredSignature |
                  InferredMethod | FallbackCall | Propagated
  is_send: Boolean
}
```

`is_send` is true only for syntactic sends and send-like nodes such as `super`,
`yield`, operators, and compound send assignments. Use the AST to count the
denominator; do not infer send coverage from the number of recorded types.

The coverage categories are:

```text
typed send       = syntactic send with a recorded concrete type
untyped send     = syntactic send with a recorded type containing Any
untracked send   = syntactic send with no recorded type at all
```

An untyped send may be intentional. An untracked send is more suspicious and
usually means an AST path was skipped, a final traversal failed to record it,
or a dynamic/generated construct was not evaluated. Report the categories
separately.

### 13.3 Strict inference gaps

After fixed-point inference, for each method in `strict` or `strong` mode,
report an inference gap if it is not explicit and any required parameter,
keyword, or return slot remains unknown/gradual. Do not report a gap for an
explicit signature merely because it contains `T.untyped`; that is an explicit
gradual contract and should be classified by origin.

`typed: false` suppresses ordinary type diagnostics for that file after mapping
back to file ranges, but parse diagnostics remain. `typed: ignore` removes the
file before registration. RBI definitions are not application send sites and
should not generate missing-API findings merely from their declaration body.

## 14. Clean-room implementation plan

An independent implementation can be built in the following increments.

### Step 1: files and spans

Implement deterministic `.rb`/`.rbi` discovery, Sorbet config ignores, built-in
RBI loading, file sigils, concatenated workspace boundaries, and offset mapping.
Test ignored vendor trees, `typed: false`, `typed: ignore`, and diagnostics in
the last file.

### Step 2: type algebra

Implement the type constructors, normalization, `join`, `meet`, `without`,
truthy/falsy parts, subtyping, recursive `contains_any`, and deterministic
printing. Unit-test `Any`, `Anything`, `Never`, nilability, generic containers,
procs, tuples, and intersections independently of Ruby parsing.

### Step 3: annotation parser

Use Prism to anchor Sorbet signatures and declarations. Add a line scanner for
`#:`, `#|`, aliases, and trailing assertions. Build parser tests for each
parameter kind, optional blocks, `T.proc.bind`, overloads, generic variables,
attached/self types, and malformed signatures.

### Step 4: declaration registry

Register method keys, scopes, singleton methods, classes/modules, ancestors,
aliases, visibility, accessors, generic members, constants, ivars, structs,
and project/built-in RBI precedence. Add fixtures where two owners use the
same method name and where an RBI types a source implementation.

### Step 5: expression evaluator

Implement literals, locals, assignments, constants, ivars, method bodies,
receiver-aware dispatch, explicit signature checking, generic substitution,
blocks, splats, and the Sorbet assertion helpers. Return `Eval` with separate
normal and abrupt outcomes from the beginning.

### Step 6: flow and structural models

Add path refinement, branch joins, loops, rescue/ensure, `return`/`raise`/
`break`/`next`, collection models, and mutation invalidation. Add a model only
when an RBI signature cannot express the relationship; keep each model
receiver- and argument-driven.

### Step 7: convergence

Add seed evaluation, method/shared dependency edges, synchronous summary
commits, changed-summary worklist scheduling, fixed-point detection, and a
final reporting pass. Test mutually recursive methods, caller-before-callee
order, shared ivar/constant changes, and a method whose block summary changes.

### Step 8: metrics and compatibility

Record every expression type and origin, derive send coverage from syntax, and
add the fixture/conformance harness. Compare against Sorbet by source span and
classify every difference before changing behavior.

## 15. Required regression matrix

The fixture suite should contain at least these independent cases:

| Area | Required case |
| --- | --- |
| precedence | source sig beats project RBI; project RBI beats built-in RBI |
| owner identity | same method name in two classes gets separate signatures |
| RBS association | `#:` and `#|` attach only to a real next declaration |
| attributes | reader annotation, writer transformation, ivar fallback |
| shape | positional/optional/rest/keyword/keyword-rest/block parameters |
| blocks | required, optional, `T.proc`, `T.proc.bind`, `define_method` |
| generics | method type parameter and generic class member substitution |
| attached types | inherited `T.attached_class` and `T.self_type` retain receiver |
| splats | tuple arity versus dynamic array/keyword splat |
| flow | truthiness, nil tests, `is_a?`, reassignment invalidation, `Never` |
| RBI boundaries | external empty declaration is gradual, not unreachable |
| coverage | recorded typed/untyped/untracked sends are distinct |
| strictness | strict reports unresolved source summaries, not explicit RBI gaps |
| generated classes | `Struct.new` block methods belong to generated class |

Every checker bug found in an application should first become one of these
small fixtures. Repository runs then act as regression checks rather than the
only specification. Spoom is the primary application check, Packwerk is a
second compatibility sample, and Rails should normally be analyzed one
component at a time while changing inference.

When comparing to Sorbet, classify differences as:

1. true program error;
2. Typey inference or flow bug;
3. missing or incorrect RBI/model;
4. unsupported Ruby/Sorbet feature;
5. intentional gradual behavior caused by `T.untyped`;
6. unvisited/untracked call or convergence failure;
7. performance problem.

Only the first category is an application defect. Categories two through four
are implementation work. Category five is not a false positive merely because
Sorbet accepts the call. Categories six and seven require coverage or
convergence fixes before diagnostic counts are compared.

## 16. Implementation traps to avoid

* **Name-only signature maps.** They attach `initialize` and `remove` to the
  wrong owner in a multi-file workspace.
* **Executing `sig` blocks.** Runtime execution cannot safely reveal arbitrary
  DSL declarations and can make analysis depend on load order.
* **One global RBI precedence flag.** Precedence is per `MethodKey` and per
  declaration source, not per file.
* **Dropping malformed comments.** A dropped block contract changes both yield
  checking and return inference.
* **Equating optional with nilable.** Omitted arguments and `nil` arguments are
  different facts.
* **Treating all missing methods as `T.untyped`.** This hides concrete receiver
  errors and destroys send-coverage evidence.
* **Treating `T.noreturn` as unknown.** It removes normal paths and affects
  reachability.
* **Erasing attached/self types.** Returning `Class` or `Object` loses a
  declared receiver relationship.
* **Using a round limit.** It conceals unstable summaries and produces
  order-dependent results.
* **Keeping flow facts after mutation or a merge.** A fact must hold on every
  surviving path and must be invalidated when the value can change.
* **Editing an application to satisfy the checker.** Fix the declaration,
  parser, model, or inference rule and add a fixture instead.

The success criterion is not merely a quiet repository. It is a checker whose
declarations are explainable, whose concrete evidence survives every phase,
whose gradual boundaries are attributable, and whose differences from Sorbet
can be reduced to a documented rule or a small regression test.
