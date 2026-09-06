# Signatures and RBIs

Inference can only be as good as the contracts it receives. Ruby source may
contain explicit Sorbet signatures, comments in RBS syntax, or no type
annotation at all. External gems and generated code are described by RBIs.
Typey combines all of these sources during declaration registration.

## What a signature contains

Typey's MethodSig records more than a return type:

- positional parameter types and names;
- required and optional parameter counts;
- rest parameter shape;
- keyword parameter types;
- keyword rest;
- block signature;
- type parameters;
- whether the method is void or abstract.

For example, this contract says that a method takes a String and returns an
Integer:

    sig { params(value: String).returns(Integer) }
    def length_of(value)
      value.length
    end

Checking a method means checking both its callers and its body. A call must
provide acceptable arguments. The body must return a value compatible with the
declared return. An explicit declaration is not an inference suggestion that
can be widened whenever the body disagrees.

## Sorbet signatures

The signature parser handles common Sorbet constructs such as:

- params and returns;
- void;
- nilable, any, all, anything, untyped, and noreturn;
- class_of;
- proc and bind;
- type_parameter;
- attached_class and self_type;
- arrays, hashes, tuples, and named generics.

Sorbet's DSL is Ruby syntax that executes at runtime, but Typey treats the
recognized forms as declarations. This avoids pretending that the type
checker can infer a useful type by executing arbitrary metaprogramming.

Helpers also have semantic behavior. T.must removes nilability at one
expression. T.cast checks the asserted target but returns the target type.
T.unsafe creates an intentional gradual boundary. T.reveal_type records a
type for inspection. These should remain distinct in the implementation.

## RBS comments

Typey also accepts RBS-style comments:

    #: (String) -> Integer
    def length_of(value)
      value.length
    end

RBS comments can describe optional parameters, rest parameters, keywords,
blocks, unions, generics, and aliases. Optionality in a parameter list is not
the same thing as a parameter whose value type is nilable:

    #: (String?) -> Integer       # argument may be nil
    #: (String) ? -> Integer      # argument may be omitted, depending on syntax

The parser must preserve the distinction represented by the actual RBS
grammar rather than normalizing every optional form into nilability.

## Attribute annotations

Ruby's attr_reader and related macros generate methods that do not have an
ordinary method definition node. A comment immediately above an accessor can
still be its contract:

    #: () -> String
    attr_reader :some_string

Annotation collection anchors this comment to the generated reader's AST
offset. It also uses ivar information when an accessor has no explicit
annotation. This is a good example of why source locations and declaration
registration must cooperate.

## RBI files

An RBI is an interface description. It gives the checker names, inheritance,
methods, constants, and signatures for code whose implementation is absent,
generated, external, or intentionally not analyzed.

There are three useful sources:

1. source declarations in the application;
2. project or gem RBIs, including Tapioca output;
3. Typey's vendored Sorbet RBI collection for Ruby and the standard library.

The checker should use RBIs to obtain types, not rewrite them merely to make
one result agree with an application. If an RBI says a field is
String | nil, the checker should respect that contract and improve its own
flow or typestate reasoning where appropriate.

An explicit source signature normally wins over a less-specific external
declaration for the same source method. A project RBI can supply a signature
for an external method. Built-in RBIs provide fallback declarations when a
method is part of Ruby's normal environment.

The key distinction is:

- a declaration with a known return type;
- a declaration whose return is explicitly T.untyped;
- a declaration that exists but has no useful signature;
- a method that cannot be found at all.

Collapsing all four into T.untyped makes metrics and diagnostics misleading.

## Lexical type names

Type names in a signature are resolved in the declaring lexical context.
Nested classes, modules, aliases, and constants can make the same short name
mean different things in different files. Registration therefore records
lexical owners and resolves names after enough declarations are known.

Do not replace an unresolved name with a globally guessed class. If the
declaration genuinely cannot be resolved, preserve the uncertainty and report
the missing contract at the appropriate boundary.

## Generic signatures

Generic signatures relate inputs, outputs, and blocks:

    sig { type_parameters(:U).params(value: T.type_parameter(:U)).returns(T.type_parameter(:U)) }

The call site binds the type parameter from its arguments and substitutes it
through the return and block contracts. This is necessary for identity-like
methods, collection transformations, and generic members in RBIs.

Type parameters are not nominal classes. An unresolved type variable is not a
safe final result. It should be solved from evidence or fall back only when
there is genuinely no evidence.

## Attached class and self type

The receiver affects some return types:

    sig { returns(T.attached_class) }
    def self.build
      new
    end

If Child inherits build from Base, Child.build should retain Child as the
attached class. Similarly, a fluent method returning T.self_type should retain
the receiver's precise type.

This requires substitution at dispatch time. Modeling every such method as
returning Class or Object loses the information that the signature explicitly
provides.

## Tracking sources of untyped

Typey records an UntypedOrigin so a broad result can be explained. Useful
categories include:

- ExplicitAnnotation;
- Unsafe;
- DeclaredSignature;
- InferredMethod;
- FallbackCall;
- Propagated.

This makes “how many untyped sends?” answerable. It also prevents a missing
method model from masquerading as an explicit application decision.

When a result is untyped, ask where it entered:

1. Was it explicitly declared?
2. Did T.unsafe or another intentional escape hatch create it?
3. Did an RBI declare it?
4. Did an unknown receiver propagate it?
5. Did a fallback call occur because dispatch or registration missed a method?

Only the last category is automatically a Typey problem, and even there the
missing contract may be the real fix.

## Fix the right layer

Use this decision rule:

| Observation | First place to inspect |
| --- | --- |
| Method or constant cannot be found | registration, owner graph, aliases, RBI loading |
| Method is found but return is too broad | signature parsing, generic substitution, evaluator model |
| A valid branch still sees nil | flow refinement, environment join, mutation invalidation |
| A generated field is nilable | RBI/schema contract and, separately, typestate facts |
| Sorbet accepts due to untyped | gradual boundary; do not call it automatically a false positive |
| A known feature is unsupported | type representation and its conformance fixture |

An RBI change is appropriate when the contract itself is missing or wrong.
Typey changes are appropriate when the contract is correct but the checker
fails to use it.
