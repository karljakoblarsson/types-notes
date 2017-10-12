% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017

Lecture 5
=========

A good complement book is Software Foundations Vol2 - Small Step operational Semantics


Normal form

$Nf e   ¬∃e' e ↦ e'$
its either `Value e` or `const n`


Strong progress Theorem
----

$∀e   \textrm{Value} e ∨ ∃e' e ↦ e'$

It means that a value is either in normal form or it's possible to evaluate it further.

How do we prove this.

### Lemma

$$
\frac{`Value` e₀   e₁ ↦ e'₁}{`add` e₀ e₁ ↦ `add` e₀ e'₁}
$$


By induction one 
```
e = const n -- e is a vlue
e = add e₀ e₁ -- by IH on e₀. 
e = add e₀ e₁ -- or by IH on e₁. 

1) Value e₀ ∨ Value e₁
2) Value e₀ ∧ ∃e'₁ e₁ ↦ e'₁ -- By using the lemma
3) ∃e'₀   e₀ ↦ e'₀
   e = add e₀ e₁ ↦ add e'₀ e₁
```

Correctness of a compiler
--------
This is a nice thing to do in Agda.

McCarthy and J. Painter (1967) published a paper about Correctness of
a compiler for arithmetic expressions.

Then it took forty years before the principles were used on C, a
'real' language.

We will prove this for arithmetic.

This is a simple machine with a stack. The stack is just a list of
Nats. $S := n : S | []$

`code` is a list of statements.

```
exp = const n | add exp exp

code = LOAD n code | ADD code | HALT

-- LOAD n
-- It pushes n on top of the stack and then considers the rest of the code.

-- ADD
-- Adds the top two element of the stack and pushes the result.

complie : expt → code
compile e = comp e HALT

comp : exp → code → code
comp (const n) cd = LOAD n cd
comp (add e₀ e₁) cd = comp e₁ (comp e₀ (ADD cd))
```

### One step evaluation
$$
\frac{}{LOAD n cd, S ↦ cd, n :: S}
$$

$$
\frac{}{ADD cd, n₁ :: (n₀ :: S) ↦ cd, (₁ + n₀) :: S}
$$

### Correctness

Semantics:
```
valOf exp → Nat
valOf (const n) = n
valOf (add e₀ e₁) = valOf e₀ + valOf e₁

-- valOf e is usally written [[ e ]]
```

### Theorem
```
compile e, [] ↦* HALT, [[e]]:[]
```

This is not possible to proove with induction. We need to strengthen
the statement first.

Theorem: $∀cd, ∀S$

```
comp e cd, S ↦* cd, [[e]] : S

∀e∀S, cd   emop e cd ↦* cd, [[e]]:S

S = []   cd = HALT   compile e ↦* HALT, [[e]]e:[]

```

By induction on e:
```
e = const e   LOAD n cd, S ↦ cd, n:S
e = add e₀ e₁   comp e₁ (comp e₀ (ADD cd)), S

IH on e₁   ↦* comp e (ADD cd), [[e]] : S
IH on e₀   ↦* ADD cd [[e₀]] : ([[e₁]] : S)
           ↦ cd, ([[e₀]] + [[e₁]]) : S
		   
```

There is not a clear distinction between syntax and semantics here.


Determinism
---

There is at most one way to reduce a term/expression. Direct proof by
induction.

$$
e ↦ e' ∨ e ↦ e''   → e' = e''
$$

Its easy to have a nondeterministic evaluation. For example, define
two different reductions for `add` one wich evaluates e₀, one that
evaluates e₁ and one which evaluates add with a constant term.


Confluence
------

The rewriting theory. It's about abstract rewriting.

__Diamond property__ of a relation R
$$
R a b ∧ R a c → ∃d (R b d ∧ R c d)
$$

__Definition__: ↦ is confluent iff ↦* had the diamond property.

Definition of ↦*
$$
\frac{e ↦ e'   e' ↦* e''}{e ↦* e''}
$$

__Proposition__: if $e$ is in normal form and $e ↦* e'$ then $e = e'$
- By case on $e ↦* e'$ 
1) $e = e'$
2) Not possible $e$ noraml form $e ↦ e'$ ⊥


__Theorem__: Iff ↦ is confluent and $e ↦* e'$  $e ↦* e''$  $e', e''$
normal form then $e' = e''$.

__Proof__: 


It does not mater how we do the computation in this system. It will
always terminate in normal form.

An example of where this does not hold:
```
e := const n | add e e | loop
-- loop ↦ loop 
```

`loop` does not satisfy `∃e' loop ↦* e' ∧ e' normal form`

__Theorem__: even with `loop` ↦ is still confluent.

$↦*$ is reflexive transitive
$↦$ is confluent
$↦*$ has the diamond property.

### This is called normalization
```
∃e' loop ↦* e' ∧ e' normal form
```


__Theorem__: if $R$ is reflexive, transitive, with the diamond
	property, then $S a b$ is defined as $∃c [R a c ∧ R b c]$
	is an equivalence relation.

$↦*$ is an equvivalence relation if $↦$ is confluent.


Untyped expression
----------

Introduce booleans in the language.
```
e := true | false | if e₀ e₁ e₂ | zero | succ e | pred e | isZero e
```

To reduce the if expression you first try to reduce e₀. If it's true
you reduce e₁, if it's false you reduce e₂.

The values in this language are:
```
bvalue := true | false
nvalues := zero | succ nvalue
```

All values are normal form.

Examples of values which are not in normal form:
```
isZero ture
succ false
```

A stuck e is a invalid program state.
```
stuck e

¬ value e
∧ nf e
```

Next time we will introduce the notion of types and a type system.
