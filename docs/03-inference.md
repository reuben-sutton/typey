# Inference: turning Ruby expressions into types

Parsing tells us what Ruby code looks like. Inference tells us what each
expression may produce. Typey's evaluator lives primarily in src/infer.rs.
This chapter explains its data structures and the route a method call takes.

## What inference is trying to compute

For every expression, the analyzer wants at least:

1. the expression's type;
2. the environment after the expression;
3. the possible control-flow outcomes.

Those are not the same thing. An expression may have type T.noreturn because
it raises, but the surrounding statement sequence also needs to know that
there is no normal environment after it. A branch may return an Integer on
one path and a String on another, so its result is Integer | String and its
post-branch environment is a conservative join.

## The analyzer's tables

The Analyzer owns the program-wide facts used during evaluation. The most
important tables contain:

- registered method states and method definitions;
- class/module names and the inheritance graph;
- aliases, accessors, and visibility;
- ivars, constants, class variables, and globals;
- type aliases and generic members;
- parameter shapes and block information;
- method dependencies and shared-state readers;
- source/RBI ranges and reporting policies;
- inferred expression types and diagnostics.

These tables let a local AST visitor answer a global question such as
“which implementation of name does this receiver call?” without repeatedly
walking every declaration.

## Method keys and receiver-aware dispatch

A method is keyed by its owner, name, and whether it is a singleton method:

    (User, "name", false)  # User#name
    (User, "find", true)   # User.find

The receiver determines the search:

1. evaluate the receiver;
2. determine its possible nominal or structural owners;
3. search singleton or instance methods as appropriate;
4. follow aliases, prepends, includes, required ancestors, and superclasses;
5. account for extension methods and class-object behavior;
6. if a union receiver has several candidates, evaluate each branch and join;
7. if an intersection receiver has compatible candidates, preserve the
   intersection's guarantees.

Receiver types can be Named, a primitive with a built-in owner, an array or
hash structure, a class object, or an attached-class form. A class object is
not interchangeable with an instance: User.new and user.new have different
dispatch semantics.

## MethodState: contract plus evolving evidence

Each method has a MethodState. Its important parts are:

- explicit signature, if one exists;
- inferred parameter slots;
- rest and keyword parameter shape;
- block/yield information;
- inferred return type;
- whether the method terminates;
- visibility and overload information.

An explicit signature is a contract. The body is checked against it, but the
signature is not widened just because one body path happens to produce a
different value. An unannotated method starts with incomplete evidence and
gets wider as calls and body evaluation reveal possibilities.

The widening operation is a join. If one call supplies a String and another
supplies an Integer, the inferred parameter becomes String | Integer.
This is conservative: the checker must accept all observed valid calls.

## The route through eval_call

Most Ruby behavior eventually passes through the call evaluator. Conceptually
it performs these steps:

1. Evaluate the receiver, if present.
2. Evaluate positional, keyword, and splat arguments.
3. Recognize type-level DSL calls such as T.must or T.cast.
4. Resolve the method candidates.
5. Apply a built-in model where Ruby's generic signature is not sufficient.
6. Check the arguments against each candidate signature.
7. Infer or check the block type and yielded values.
8. Substitute generic variables and attached/self types.
9. Compute the return type, setter result, safe-navigation nilability, and
   termination.
10. Record dependencies, untyped origins, and diagnostics.

The spelling in the source is important. A setter such as value = x has the
value assigned as its expression result in Ruby, while a normal method call
uses the declared return. Safe navigation adds nil only on the path where
the receiver can be nil.

## Explicit signatures and inferred methods

Consider:

    sig { params(value: String).returns(Integer) }
    def size_of(value)
      value.length
    end

The signature supplies the parameter and return contract. The body is checked
against it. If the body returns a string, that is a contract violation; Typey
must not silently widen the declared result to Integer | String.

Without a signature:

    def size_of(value)
      value.length
    end

the checker gathers evidence from call sites and from value.length. If the
receiver type is unknown, the method may remain incomplete. In typed: true,
that can be reported as a coverage or missing-API issue; in typed: strict,
insufficient method summary information is also reported.

## Argument checking

Signatures describe required and optional positional parameters, rest
parameters, keyword parameters, keyword rest, and blocks. Checking needs to
distinguish:

- too few or too many positional arguments;
- a positional argument passed where a keyword is required;
- unknown keywords;
- an argument whose type is not a subtype of the parameter type;
- a block that yields the wrong number or type of values;
- a splat whose shape is known, partially known, or unknown.

Known tuple and array types are especially valuable for splats. A tuple
preserves positional arity; an ordinary array generally represents repeated
elements. The checker should use that evidence before falling back to a
gradual result.

## Generic substitution

Suppose a method has a return type involving U:

    identity("hello")  # U is bound to String

The call evaluator unifies argument evidence with parameter types, builds a
substitution such as U -> String, and applies it to the return and block
types. This same mechanism handles generic collection methods and generic
members declared in RBIs.

An unresolved type variable is an inference failure, not a valid final type.
Keep the failure local and use T.untyped only if there is no concrete
evidence from any input or declaration.

## Blocks are typed values

Ruby blocks are not merely syntax attached to a call. They are callable
contracts. A method signature can say what arguments it yields and what the
block returns. The evaluator:

- binds each yielded value in a block environment;
- checks block parameters against the yield shape;
- infers the block body;
- feeds the block result into methods such as map, reduce, or
  each_with_object;
- preserves break, next, and return as distinct control-flow outcomes.

Some built-in collection operations need a model because a simple method
return type cannot express the relationship between an input element and a
block result. map changes the element type; select preserves it; reduce
carries an accumulator; to_h changes collection shape.

## Built-in evaluator models

RBIs are the normal source of contracts. A built-in model is appropriate when
the Ruby operation has a type relationship that cannot be represented
adequately by the available signature form, or when the operation's behavior
is fundamental to inference.

Current model families include arrays, hashes, strings, numerics, global
helpers, sorting/node helpers, and common Sorbet operations. A model should:

- inspect the actual receiver and argument types;
- preserve concrete element/key/value types;
- type the block using the operation's real yield shape;
- report invalid argument combinations;
- return a principled gradual type when the input is genuinely unknown.

Do not add a model merely because a particular application calls a method in
an unusual way. First check the vendored RBI collection and ordinary dispatch.

## Recursive inference and the worklist

Inference is a dataflow problem over a graph:

    caller -> callee

The return summary of the callee affects the caller's expression type. The
caller may in turn affect the inferred parameter slots of the callee. Cycles
therefore require repeated evaluation.

Typey uses a worklist and changed-summary scheduling:

1. Take a method from the queue.
2. Evaluate it against committed summaries from the prior state.
3. Produce a candidate return and parameter summary.
4. Commit the candidate.
5. Requeue callers if the return changed.
6. Requeue readers if shared declarations changed.

The queue is a dependency mechanism, not just a loop counter. If a method is
being evaluated over and over, inspect which input changed and why. Broad
invalidation, unstable union normalization, or a dependency recorded for
every possible method are typical causes.

## How to investigate a surprising inferred type

Start at the expression and work outward:

1. What AST node produced it?
2. What was the receiver type immediately before the call?
3. Which MethodKey candidates were found?
4. Which signature or built-in model won?
5. What substitutions were made for type variables or attached types?
6. Was a block or splat involved?
7. Did safe navigation add nil?
8. Did a prior branch refinement survive the environment join?
9. Did an explicit T.untyped or unsafe boundary enter the result?
10. Did a fallback call occur because a declaration was genuinely missing?

This sequence distinguishes a bad type operation from a missing declaration,
a dispatch bug, a flow bug, and an intentional gradual boundary.
