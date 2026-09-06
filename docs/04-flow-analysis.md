# Flow-sensitive analysis

Ruby variables do not have one type for the whole method. Their possible
values change after predicates, assignments, loops, exceptions, and early
returns. Typey tracks these changes with an environment and explicit control
flow.

## The environment

An Environment is the local state at one program point. It contains:

- local variable types;
- open-array locals whose elements may be assigned later;
- predicate aliases;
- known truthiness facts;
- the current self type;
- the current method key.

Reading a local asks the environment first. If it has no binding, inference
must distinguish an unknown local from a local known to contain nil or
T.untyped.

Binding a local updates its type and clears stale facts about its previous
value. In particular, reassignment invalidates an open-array fact, predicate
alias, and truthiness fact when those facts no longer describe the value.

## Branching

For an expression such as:

    if value.nil?
      value.to_s
    else
      value.length
    end

the checker:

1. evaluates the predicate;
2. derives a true-branch environment;
3. derives a false-branch environment;
4. evaluates both branches;
5. joins the branch result types;
6. joins their environments at the merge point.

The true environment can narrow value to nil; the false environment can
remove nil from its type. The post-if environment must be conservative.

A fact is retained after a merge only if it is valid on every normal incoming
path. If one branch assigns value and the other does not, the result may need
to include nil or the prior value. Retaining a fact from only one branch
creates unsoundness.

## Predicate normalization

The narrowing code recognizes predicates in a normalized form rather than
only one surface syntax. Useful forms include:

- value and !value;
- value.nil?;
- value.is_a?(String);
- kind_of? and instance_of?;
- class === value checks;
- equality and inequality with nil or literal values;
- parenthesized expressions;
- && and ||;
- aliases such as ok = value.nil?;
- ivar predicates and safe-navigation conditions.

Conjunction refines both facts where appropriate:

    value.is_a?(String) && value.length > 0

Disjunction must preserve alternatives. It is unsound to apply the left side's
narrowing to the entire right side unless the logical structure proves that
fact. Parentheses and evaluation order matter.

## Truthiness and nilability

Ruby's falsey values are nil and false. A truthy branch can therefore remove
those alternatives when the type representation supports that proof. It does
not prove arbitrary object state.

For example, a database-backed field may be typed as String | nil because a
record can be new or because the column is nullable. A check that a record is
persisted can establish a typestate fact about the record, but it must not
pretend that a nullable column is non-null unless schema metadata says so.

Likewise, T.must(value) is an assertion at a specific point. It should remove
nilability from that result according to Sorbet's semantics, but it should not
globally mutate the type of every future read of value.

## Predicate aliases

Ruby applications often assign a predicate to a local:

    present = !value.nil?
    if present
      value.length
    end

Typey records the relationship between present and the underlying predicate.
The alias is valid only while the referenced value and the predicate meaning
remain unchanged. Reassigning either side must invalidate the alias.

This is more general than hardcoding one block or local variable name. The
same mechanism can support helper predicates when their assertion contract is
declared.

## Abrupt control flow

An expression has both a type and a flow bitset. The flow tracks normal
completion and abrupt outcomes such as:

- return;
- raise;
- break;
- next;
- retry.

For a statement sequence, the next statement receives only environments from
normal outcomes. A raise expression has T.noreturn as its normal type and
does not create a reachable normal successor. A return contributes its value
to the enclosing method summary but does not contribute a post-return
environment.

This distinction prevents a common bug: treating T.noreturn as merely an
ordinary type while still evaluating code that cannot run.

## Loops

A loop can execute zero times or many times. Typey therefore cannot simply
use the body environment as the after-loop environment. It evaluates a
conservative loop invariant:

1. start with the environment before the loop;
2. evaluate the condition and body;
3. join the body result back into the loop-entry state;
4. repeat until the local facts stabilize;
5. join the zero-iteration and completed-loop paths.

For loops and iterator blocks also need to account for the element type and
for variables that remain visible after the loop, as Ruby permits.

## Assignment and mutation

An assignment changes facts:

    value = "text"
    value = nil

After the second assignment, value is nil on that path. Mutating an object
does not necessarily change the nominal type of the object, but it may
invalidate structural facts. Appending to an array can widen its element type;
writing a hash key can widen its value type; calling an unknown mutating
method may require losing a refinement.

The safe rule is to invalidate only facts that the operation could change.
Invalidating everything destroys useful precision; invalidating nothing is
unsound.

## Exceptions and rescue

An exception edge is another path. A method body can have:

- a normal result;
- a raised result;
- a rescue result;
- an ensure effect that runs on both.

The checker should join environments from paths that actually reach the
merge. An exception raised before an assignment does not prove that the
assignment happened in the rescue branch. Ensure is evaluated for its effects
while preserving the original return or raise behavior.

## ActiveRecord as a future typestate extension

ActiveRecord illustrates why ordinary nominal types are not enough. A model
instance can be the same class while being new, persisted, or destroyed.
Generated Tapioca fields often become either T.untyped or Type | nil. Those
choices are safe but lose useful application safety.

A principled extension would track an object-state fact alongside the nominal
type:

    User & state(new)
    User & state(persisted)
    User & state(destroyed)

The flow checker could refine the state after contracts such as persisted?,
new_record?, or a successful save. It would then use field metadata to decide
which reads are non-null in the persisted state. Persistence alone must not
remove nil from a nullable column.

This should be implemented as an extensible fact domain:

1. define a fact key and its possible states;
2. define predicate refinements;
3. define state transitions for known mutators;
4. define join behavior at control-flow merges;
5. keep nominal type and object state separate;
6. add fixtures for every refinement and invalidation rule.

Do not solve it by changing every model field from nilable to non-nilable or
by special-casing one application's model names.

## How to debug a flow bug

Reduce the report to one local and one branch. Then inspect:

1. the type before the predicate;
2. the true and false refinements;
3. the flow outcomes of each branch;
4. the environment join;
5. assignments or mutating calls between predicate and use;
6. whether the fact was intended to be a type fact or an object-state fact.

If a fact survives a merge where it should not, fix Environment::join or the
fact's meet/remove operation. If it disappears too early, find the operation
that invalidated it and make invalidation precise.
