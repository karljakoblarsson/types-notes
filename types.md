% Types for Programs and Proofs - DAT350
% Jakob Larsson <jakob@karljakoblarsson.com>
% Lp1 2017

<!--Administrative stuff-->
<!------------------------>
<!--https://www.cse.chalmers.se/edu/year/2017/course/DAT350/-->
<!--- Take home exam 2017/10/17 08:00 – 2017-10-20 12:00-->
<!--- Presentation of one advanced topic, a chapter of the book or a research-->
  <!--article. You also need to opposite an other talk.-->
<!--- Home work, is optional for bouns points-->
<!--- Oral exam fro grade 4 or 5.-->

Lecture 1
=========

There are many techniques for improving software quality, both from software
engineering and computer science.

In this course we will look at a programming language designed for correctness:
Agda. Along with mathematical techniques for specifying and reasoning about
properties about programs and tools used to validate thoose properties.

What are types?
---------------

Types are not nessescary, assembly dosen't have types.

This is a sort of continum of more and more advaced and powerful types of
types:

- Int, char – eg Fortran
- Types of functions, objects, reference, records – eg Simula
- Recursive types – Functional languages.
- Polymorphic types
- Abstract types
- Dependent types
- Subtypes
- …

Typed functional programming languages:
- Haskell – lazy
- Ocaml, SML – strict
These have recursive, polymorphic and abstract types.

Purpose of types
----------------
- Specification
In some ways types are a lightweight specification of the program. And
a runnable documentation of the programmers intent.

- Bug-finding

- Optimization
To reserve the nessescary abount om memory but not more.

### Type chincking
- Correct number of function arguments
- Apply function to the wrong type
- Use of undeclared variables
- Division by zero
- Array indices out of bounds
- Non-terminationg recursion
- Sorting algorithms that don't sort

Programming languages are different, every languages checks a different subset.

The usefulness of this depends on the richness of the type system.

Types can enforce abstractions and modularity.

You can use Agda as an interactive proof system for logic system, including
predicative logic.

Agda
----

Agda is a functional language with dependent types. The big picture is similar
to Haskell or ML. (Haskell has generalized abstract types witch is similar to
depentent types)

### Dependent type
> Vect A n
A vector witn n elements of type A. Depends on the type A:Set(type of "small
types") and length n:Nat.

### Termination checking
You can only write programs with terminates. But it is possible to turn of the
termination checker.

These two features are _ for Agda and makes it possible to use as a proof
system.

These two things makes it possible to use the Curry-Howard identification.
> proposition (formula) => types

In the 1930s it was discovered that simple types can encode propositional
logic.
Curry-Howard was found quite late and extended type system to be able to encode
predicative logic. Martin-Löf (1972) got the idea that this could be used as
a programming language. The first systemes in 1980s started at Cornell and
Chalmers.

The current version of Agda started in 2005.

The premiere way to develop Agda is with Emacs as an interface. (damn it)
There is a way to do programming and proving with Agda by pointing and
clicking.

(Is there a way to start the programming in a very flexible language like JS
and then gradually specify more and more in a very rich type system like Agda?
A big but really interesting question.)

Agda has a nice mixedfix syntax and good unicode support.

Each file in Agda has to be a module, and in a file with the same name as the
module.

``` Agda
module Bool2017 where

-- Definition of bool in Haskell: data Bool = True | False
-- You need to declare it as a small type. There are bigger types so it needs to
-- be explicit defined.
-- An empty type is a proposition with no proof. Which of course is false.
-- data Bool : Set where

data Bool : Set where
  -- Constructors with lowercase compared to Haskell. A constructor can take
  -- a more complex type. Type def is a single colon and cons is a double.
  -- (flipped compared to Haskell)
  true : Bool
  false : Bool

not : Bool → Bool
-- This is ok in Agda, to say that we don't know what the expression should be.
-- ^c^l Load. ^c^c create pattern match
not b = ?
-- Run ^c^c
not true = { }0
not false = { }1
-- Fill in the definition
not true = false
not false = true
-- ^c^space "give" (fill in hole by complete term)

notnot b = not (not b)

_&&_ : Bool → Bool → Bool -- Declare an infix operator. You need spaces around
-- the operator when using.
b && b' = b'
b && true = b
b && false = false

infixl 20 _&&_ -- Declare the precedence between 0 and 100. Infixl for left
associative, infixr for right assoc.

in_then_else : Bool → Bool → Bool → Bool
if b then c else c' =
if true then c else c' = c
if false then c else c' = c'

```

In Agda there is no built in integers. Agda is built for proving and from that
view integers are quite complex. It is not obvious how use binary numbers.

```
data nat : Set where
  zero : Nat
  succ : Nat → Nat

one = succ zero
two = succ one
```

You can get decimal notation and machine artihmetic.
