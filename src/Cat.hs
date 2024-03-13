{- | This module is a documentation entry point for the package — nothing is
exported here.

General introductory remarks are available in the project cabal file and the
README. Concrete, relatively self-contained examples are in the README and in
modules that have "Examples" in the path.

If you are still getting acquainted, then you may wish to skip to the second
section on the basic representation of the package.
-}

{- TODO
Use tables!

-}

module Cat
  (
    -- * Finding what you need in the package and importing it
    -- $navigation


    -- * The basic representation of this package
    -- $basicRep

    -- * Typeclass hierarchy overview
    -- $hierarchyOverview
  ) where


{- $navigation

== Haddock readability

As noted in the README and the project description, no Haddock theme currently
copes well with type variables that take up a lot of space (e.g. when explicitly
kinded) or with large sets of constraints. That means looking at the source code
may often be easier than browsing the Haddock-generated documentation. (Forcing
existing Haddock themes to put function arguments on separate lines from
constraints is also the motivation for some Haddock annotations that "document"
obvious information.)


== Imports

There's a finite amount of short ASCII identifiers, and to avoid cryptic
suffixes or obligatorily verbose identifiers while also providing exactly the
name you would expect for identifiers that are direct analogues or
generalizations of existing functions or classes, this package is designed to be
used with qualified imports ± by hiding clashing identifiers.

@
import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zipWith
  , ...
  )
@

To accomodate preferences around namespace clashes and ASCII vs. Unicode, a few
synonyms for clashing operators are typically provided in a given module.

You may also wish to adopt two other conventions used in this package: to avoid
ambiguity, @∘@ is typically used for normal Prelude composition of @(->)@ and
@⊙@ is used elsewhere for composition of morphisms in a given monoidal category.

Because there is often overlap for a given @x@ between @Cat.Unsized.x@ and
@Cat.Sized.x@ modules (e.g. @Cat.Unsized.Functor@ vs. @Cat.Sized.Functor@), it
is common in the package for @Unsized@ vs. @Sized@ variants of a given
identifier to be disambiguated by a @U.@ or @S.@ qualifier in contexts where
overlap occurs.


== Where do I find...?

Generally instances that you might want to replace are in @....Instances@ and
everything else is in @....Class@ or @....Data@. The module one level up from
@....Instances@ and @....Class@ (or @....Data@) re-exports both sets of definitions.

Modules for free category types (e.g. free categories, free SMCs, etc.) follow
the same principles. Such modules are separate from each other for namespace
reasons (they have overlapping identifiers), mainly because the expectation is
that, for any module where a free category type is imported, there will
typically only be one such type used.
-}




{- $basicRep

The basic morphism type you will see throughout this package is

> k φ n m a b

where

> k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type   -- A monoidal category morphism type.
> φ ∷ Nat → κ → κ                                -- A monoidal product functor, indexed by a Nat representing the size of the product.
> n ∷ Nat                                        -- The size of the source object.
> m ∷ Nat                                        -- The size of the target object.
> a ∷ κ                                          -- The source object type.
> b ∷ κ                                          -- The target object type.

Instead of @k φ n m a b@, in this package you will typically find sugared
syntax

>   k φ n m a b
> ≡ a -| k φ n m |-> b

that simulates a mixfix operator with a pair of infix operators @(-|)@, @(|->)@
from "Cat.Operators" to improve readability — particularly of source code, and
to a lesser degree Haddock.


/Why is this the basic morphism type? What does this represent? Why is it more/
/verbose than what you might be expecting? How does the hierarchy of/
/typeclasses built on it relate to category theory concepts in a more general/
/setting?/

The nub of the answer to these questions is summarized below:

 - __What does that morphism type represent?__ For a category /k/ with finite
   /n/-ary monoidal product functor /φ/ (where /n/ in general can vary), a
   morphism type

   > a -| k φ n m |-> b

   describes a morphism from /n/ copies (values) of the object (type) /a/ —
   glued together with /φ/ — to /m/ copies of the object /b/ — glued together
   with /φ/.

 - __Why are arrows always to and from products? Why is the type so verbose?__
   Steering clear of the ergonomic costs of heterogenously-typed collections,
   holding GHC's hand for type-inference, enforcing that certain monoidal
   properties hold without resort to plumbing combinators, and because there are
   a healthy number of domains where finite (co)products indexed by /ℕ/ are a
   decent or great domain fit.

 - __How do the various category typeclasses in this package relate to categories__
   __that don't have all these seemingly disparate restrictions?__ I've tried not
   to put too fine a point on this, but to my knowledge as someone who's not a
   category theory expert, there are a few directions for interpretation:

       - __Special cases + pragmatism__. Do you really need to know that an
         @Applicative@ functor is a
         [\"strong lax monoidal endofunctor on the cartesian closed category `->`\"](https://cstheory.stackexchange.com/a/16264)
         to use it effectively? For many cases, no, not at all. From this
         perspective, in a similar way that categorical concepts have made their
         way into Haskell with simplifications for the special case of the
         ambient category (`->`) that matters most, the typeclasses of the
         @Cat.Sized.x@ modules in this package should be written as and readable
         as specializations of the general concepts for the setting described
         above — you shouldn't /need/ to read any of the category theory-focused
         references in the @Resources@ section of the @README@ to understand
         enough about what any typeclass in this package models well enough to
         use it.

      - __The pragmatically motivated and seemingly-disparate restrictions are__
        __maybe not so disparate after all__. Oddly enough, there are a variety
        of generalizations of the basic notion of a category where, instead of
        morphisms /a → b/ always relating a single source object to a single
        target object, they

            - Have an input ("source") that is a finite /n/-ary product
              \( a^n \) of one object \( a \) from the underlying category.
            - Have an output ("target") that is a finite /m/-ary product
              \( b^m \) of one object \( b \) from the underlying category.

        I wouldn't claim to be an expert on these abstractions and didn't have
        them in mind when I started writing this package. Note that these
        abstractions vary in whether

          - Their basic version vs. further extension or generalization allows
            for the category to have more than one object (i.e. whether the
            category is "many-sorted" or "polychromatic").
          - Their basic version vs. further extension or generalization allows
            for not only multiple inputs, but also multiple outputs.
          - How composition works.

        For more on these generalizations, you can look up "multicategory",
        "operad", "Lawvere theory", "concategory", "polycategory", \"PROP\", or
        "properad" for yourself; there are some links in the __Resources__
        section of the README, including a few that contain Haskell (focused on
        operads). The punchline is that "many-sorted PROPs" or "concategories"
        most closely correspond to the @Monoidal@ category typeclass of this
        package.

        The pragmatic significance of this is summarized by the comparison below:

           - In a (Cartesian) closed setting like @(->)@ (or an otherwise
             sufficiently simple category), a term corresponding to a "program"
             in a DSL modeled in terms of categories is
             /a path in a directed graph/ whose vertices are types and whose
             edges are morphisms.

           - In a monoidal category of the kind modeled by this package, a
             program in a DSL is essentially /a path in a directed hypergraph/ —
             modulo some bookkeeping scheme used to impose an order on vertices
             of a source or target.


If that's enough information, you can skip ahead to the overview of the
typeclass hierarchy. Otherwise, immediately below is a more thorough motivation
of the basic morphism type plus the design decisions and trade-offs behind it.


== Problem: ergonomics of binary Cartesian (co)products

Without rehashing too much of the motivation presented elsewhere, the pragmatic
starting point is that if we want to represent (co)cartesian categories in
Haskell — where we must be more explicit about equality vs. isomorphism and
where not every categorical concept is expressible — the simplest starting point
is to use @(,)@ and @Either@ to represent binary products and coproducts,
respectively.

Given this choice, we need explicit morphisms for re-association and to
introduce or eliminate the unit with respect to the (co)product. See the Elliott
references in the README or the
[@constrained-categories@](https://hackage.haskell.org/package/constrained-categories-0.4.2.0/docs/Control-Category-Constrained.html#g:2)
package for examples.

If we want to represent products of non-trivial size — or perform other
operations on them (indexing, duplication, @fmap@ing, ...) — without saying
anything about premature concerns about performance, there is a high marginal
ergonomic cost to be paid at usage sites for the simplicity of design of
(co)products, simplicity of representation of (co)products, and the
accessibility of this representation.


== Problem: for EDSLs, you want more general representations anyway

If your domain is not best (or at all) represented by Cartesian (co)products or
binary ones in particular, or you want to interpret your EDSL into a type from
some domain with those qualities, you probably want typeclasses that let you
represent non-binary, non-Cartesian (co)products without too much friction.


== Solution: Choose your functor

If a type for representing monoidal category arrows /k/ were parameterized by a
choice of product functor /φ/, then all else being equal, users of the type
could use whatever monoidal (co)product functor they pleased, including one
whose arity is more general than a strictly binary (co)product.

Similarly, if the functor type helped enforce (or completely enforced) monoidal
properties like associativity or the existence and behavior of an identity, that
would also help cut down on boilerplate at the term level at sites of use.


== Trade-offs: You can choose any monoidal product functor you like, as long as it's @Nat@-indexed

- __Homogeneously-typed products__: By giving up tuples for flexibility in
choosing an /n/-ary functor, we give up heterogeneously-typed products...unless
we were to decide to make use of one of the Haskell libraries for
heterogeneously-typed collections. (This package does /not/ use heterogeneously
typed collections and has more than enough complexity as-is between constraints
and type-level @Nat@-indexed products.)


- __Pros of @Nat@-indexed functors — monoidal properties__: We can capture some
monoidal properties at the type level with functors representing ordered
collections that are indexed by a typelevel-@Nat@ indicating the cardinality of
the collection:

    - The monoidal product of \( a^n \) and \( a^m \) — @φ n a@ and @φ m a@ — is
      given by addition of the cardinalities and concatenation of the two
      collections. Associativity is enforced (up to implementation permutation
      of elements) by the concatenation operation.
    - The identity element with respect to the monoidal product is the length
      zero product \( a^0 \).


- __Pros of @Nat@-indexed functors - correctness__: Fiddly index bullshit is
tedious and error-prone, and it's no accident that functional programming tools
(@map@, @fold@, etc.) for iteration and control-flow often encoded in stateful
imperative languages by indexing and loops is one of the first things a
functional programmer is introduced to. Using @Nat@-indexed types can make it
easier to write some code period, or easier to write it correctly and with
confidence.

    From writing `->` instances for @vector-sized@ and @orthotope@ types in this
    package, I can offer the following anecdata in support of this: while the
    two packages are not apples-to-apples comparable in development time, what
    they can represent, or what dependently-typed features they would need to
    offer comparable type-safety, @vector-sized@ offers (enforces) more
    type-safety than @orthotope@. When implementing very similar code for both,
    @vector-sized@ frequently catches bugs at compile time that I missed in an
    earlier @orthotope@ implementation, "if-it-compiles-probably-works" is not
    as reliable when working with @orthotope@, and runtime errors are a
    comparatively more common feature feature of both testing and of learning
    the API.

- __Cons of @Nat@-indexed functors__:

    - /Domain modeling/. As noted in the README, sometimes distinguishing
        collections with different arities as different types makes it easier
        for types to accurately model your domain, but this is sometimes false
        in subtle or hard-to-predict ways.

    - /Papercuts/. Type-level @Nat@s are a fancier Haskell feature, and can be
    brittle or frustrating: Haskell is not a dependently-typed theorem proving
    language, and while its type system continues to /evolve/ into a more richly
    featured second programming language relative to the term level, GHC is not
    as good at reasoning about @Nat@-manipulating code as a real
    dependently-typed language is. Sometimes perfectly good code won't typecheck
    and in other cases the resulting types or implementation are obfuscated by
    mechanisms for convincing the compiler that something is correct. Much of
    this package is an experiment to see what the cost vs. benefit ratio is in
    the domain of categorical DSLs.

        In particular, the general verbosity of the basic morphism type in this
        package and especially the assumption to limit morphisms to /always/ having
        an ambient product on their source and target objects are both motivated by
        making it easier to write code that typechecks.

-}



{- $hierarchyOverview

The typeclass hierarchy divides into two components.

The first — @Cat.Unsized....@ — contains a smaller basic set of typeclasses for
abstractions that don't (neccessarily) have a monoidal functor (@Nat@-indexed or
not) involved.

== Unsized

@
Semigroupoid (k ∷ κ → κ → Type)

Semigroupoid k ⇒ Category k

(Category l, Category r) ⇒ Profunctor l r p

(Category r, Category t) ⇒ Functor (φ ∷ κ → κ') r t

(Category r, Category t) ⇒ NatTrans (φ ∷ κ → κ') (γ ∷ κ → κ') r t

Functor φ k k ⇒ Monad φ k

Functor φ k k ⇒ Comonad φ k

(Functor φ k k, Functor γ k k) ⇒ Distributes φ γ k  -- For describing distributivity of a comonad+monad pair
@

At first glance, the main sources of potential surprises here are that

 1. Because we are no longer assuming that everything of interst lives in
    @(->)@, @Functor@ and associated typeclasses need one or two type parameters
    indicating the relevant categories.

 2. Because we are no longer assuming that everything of interest lives in a
    Cartesian closed category (viz. @(->)@), some combinators (@fmap@, bind)
    whose familiar form is curried or infix are neither.

 3. @Semigroupoid@ and @Category@ have associated constraints (not visible from
    the summarized hierarchy above) for defining which properties a type must
    have to be considered an object of a given semigroupoid or category.

This hierarchy is much smaller than the otherwise parallel one for categories
with finite homogeneous monoidal products; typeclasses in this hierarchy
(@Cat.Unsized....@) serve a few purposes:

 1. They serve as a stepping stone for promotion of existing @base@ typeclass
    instances for @(->)@ into the @Sized@ hierarchy.
 2. Lifting "sized" morphisms @a -| k φ n m |-> b@ from a monoidal category
    (@Cat.Sized.Monoidal@) to @γ i a -| k φ n m |-> γ i b@, for some sized
    functor @γ ∷ Nat → κ → κ@, where @γ@ is often @φ@.
 3. Temporarily forgetting size information on an arrow from a monoidal
    category.


== Sized

The basic hierarchy of @Cat.Sized...@ — stripped of the specialized typeclasses
for monoidal categories — is below:

@
Semigroupoid φ k

Semigroupoid φ k ⇒ Category φ k

Category φ k ⇒ Monoidal φ k

(Category φ l, Category γ r) ⇒ Profunctor φ l γ r p

(Profunctor φ l γ m p, Profunctor γ m η r p) ⇒ ProSG φ l γ m η r p

(ProSG φ l γ m η r p, Category φ (p φ), Category γ (p γ), Category η (p η)) ⇒ ProCat φ l γ m η r p

(Category φ r, Category γ t) ⇒ Functor η φ γ r t

(Category r, Category t) ⇒ NatTrans φ γ r t

(Functor γ φ φ k k, Monoidal φ k) ⇒   MonoidalEndo γ φ k
(Functor γ φ φ k k, Monoidal φ k) ⇒ OpMonoidalEndo γ φ k

Zip φ k

MonoidalEndo γ φ k ⇒ TraversableEndo γ φ k
Functor γ φ φ k k ⇒ DistributiveEndo γ φ k

Functor γ φ φ k k ⇒   Monad γ φ k
Functor γ φ φ k k ⇒ Comonad γ φ k

(Functor γ φ φ k k, Functor η φ φ k k) ⇒ Distributes γ η φ k   -- For describing distributivity of a comonad+monad pair
@

=== Focus on @Monoidal@

To understand this hierarchy, start by taking a closer look at @Monoidal@: none
of the other typeclasses here make much sense outside of the context of that
typeclass: any /φ/ and /k/ that has e.g. a @Cat.Sized.Semigroupoid@ instance
probably ought to have a @Monoidal@ instance, and the rest of the typeclasses
present here are artifacts of working in Haskell and making it more convenient
to work with @Monoidal@ morphisms.


==== Morphisms in @Monoidal@ + what about coproducts?

Note that /every/ morphism @a -| k φ n m |-> b@ is to and from a finite
(co)product, and both source and target (co)products as well as the
cardinalities are part of the type of every morphism:

 - The basic assumption is that the most typical use case involves a category
   with one monoidal product functor — so the source and target product functor
   are assumed to be the same and accordingly @Semigroupoid@, @Category@,
   @Monoidal@, and many of the subtypes of @Monoidal@ only have one type
   parameter for a (co)product functor.
 - Profunctors are the tool for handling categories with multiple distinct
   (co)products: such arrows have the type @a -| k φ γ n m |-> b@.


==== Other typeclasses that come with the territory

For any /φ/ and /k/ that has a @Monoidal φ k@ instance, /φ/ is probably an
@Applicative@, @Traversable@, and @Representable@ functor (ie. in the context of
the cartesian closed category `->`).

Currently the @Monoidal@ typeclass includes methods that only make sense for
categories where nested products (i.e. monoidal product functors that are also
/monadic/) are permitted; in principle this may not fit some domains and it
means extra obligatory work to define an instance and start exploring design
decisions or test things. Consequently, those methods may be split off into a
separate typeclass.


==== Note on a likely use of @fmap@ with @Monodial@ arrows

Finallly, note that as a result of the type of morphisms and the current
definition of @Cat.Sized.Functor@, @fmap@ by default makes it easy to introduce
functors (sized or otherwise) "inside" the ambient ("outermost") product
functor: if @f ∷ a -| k φ n m |-> b@ and you want to lift @f@ to a morphism that
acts on @l@ copies of input values of the appropriate shape, then supposing @φ
l@ is the functor you want to lift @f@ into, the type you can get with @fmap@
alone (i.e. @fmap f@) is

>>> φ l a -| k φ n m |-> φ l b

This is an artifact of the final two type arguments of a morphism reflecting the
type of the value /inside/ the outer /φ/ product layer plus the currently
enforced property that @fmap@ in @Cat.Sized.Functor@ must preserve the source
and target cardinalities.

If what you want is a morphism of type

>>> φ n a -| k φ l l |-> φ m b

then there is a combinator (@omap@) in "Cat.Sized.Monoidal" that makes this
possible. Adding another typeclass for endofunctors that makes this more
convenient (and more customizable than the current combinator) might be a
reasonable concession to ergonomics, but is not currently a priority.


=== Substructural types or logics and why you might (not) want refinements of @Cartesian@ or @Cocartesian@ for your domain or for DSL development

If you are uncertain why someone might want a typeclass hierarchy that can make
finer-grained distinctions than @Cartesian@ or @Cocartesian@ categories, a
satisfying answer is out of scope for this package's documentation. See e.g.

- [Substructural type system](https://en.wikipedia.org/wiki/Substructural_type_system)
- [Substructural logics](https://plato.stanford.edu/entries/logic-substructural/)
- [linear-smc](https://hackage.haskell.org/package/linear-smc) or the accompanying
  [paper](https://arxiv.org/abs/2103.06195)
- resources about [Markov categories](https://ncatlab.org/nlab/show/Markov+category)
- resources about [concatenative programming languages](https://www.dawn-lang.org/posts/foundations-ucc)
- [What does a nontrivial comonoid look like?](https://stackoverflow.com/a/23858109)
- [The "reader" monad](https://stackoverflow.com/a/15419213)
- ...or other resources — some of which you might find in the __Resources__ section
  of the github README — about the relationship between substructural
  logics/types, categorical logic, the Curry-Howard isomorphism, and models of
  computation.


=== Substructural refinements of @Cartesian@

@
Monoidal φ k ⇒ Braided       φ k  -- Provides the ability to swap a pair of product elements.
Monoidal φ k ⇒ Permutable    φ k  -- Provides the ability to permute every element of a product.

Monoidal φ k ⇒ Diagonal      φ k  -- Provides the ability to replicate every element of a product some number of times.

Monoidal φ k ⇒ Semicartesian φ k  -- Provides the ability to index into a product to get one element, destroying all copies of other elements.
Monoidal φ k ⇒ HasTerminal   φ k  -- Provides the ability to destroy all copies in a product.
Monoidal φ k ⇒ Delete        φ k  -- Provides the ability to destroy one element of a product and leave others unchanged.
Monoidal φ k ⇒ Select        φ k  -- Provides the ability to take a contiguous "slice" of elements from a product.

(Braided φ k, Diagonal φ k, Semicartesian φ k) ⇒ Cartesian φ k
@

Note that because I don't think there's a way to encode the distinction between
braided and symmetric monoidal categories in Haskell and I'm not currently
familiar with a pair of closely related examples that I might want to
distinguish between, there's no distinction between the two in this hierarchy.


=== Substructural refinements of @Cocartesian@

@
Monoidal φ k ⇒ Braided       φ k    -- Provides the ability to swap a pair of product elements.
Monoidal φ k ⇒ Permutable    φ k    -- Provides the ability to permute every element of a product.

Monoidal φ k ⇒ Codiagonal    φ k    -- Provides the ability to fold (eliminate, \'jam\') a coproduct.

Monoidal φ k ⇒ Semicocartesian φ k  -- Provides the ability to inject one element into a coproduct.
Monoidal φ k ⇒ Pad             φ k  -- Provides the ability to inject a contiguous "slice" of elements into a coproduct.

(Braided φ k, Codiagonal φ k, Semicocartesian φ k) ⇒ Cocartesian φ k
@


=== Categories with more than one monoidal (co)product structure

@
( Monoidal     φ (k φ)
, Monoidal     γ (k γ)
, Profunctor   φ (k φ) γ (k γ) k
, Profunctor   γ (k γ) φ (k φ) k
) ⇒ Bimonoidal φ γ k

( Semicartesian   φ (k φ)
, Semicocartesian φ (k φ)
) ⇒ Semiadditive  φ  k

( Braided    γ (k γ)
, Monoidal   φ (k φ)
, Profunctor φ (k φ) γ (k γ) k
, Profunctor γ (k γ) φ (k φ) k
) ⇒ DistributiveLR φ γ k

(   Cartesian    φ   (k φ)
, Cocartesian      γ (k γ)
, DistributiveLR φ γ  k
, DistributiveLR γ φ  k
) ⇒ Bicartesian  φ γ  k
@

-}
