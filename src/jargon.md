================================================================================
an extremely opinionated jargon file for category theory
================================================================================

this file serves as my working understanding of the terminology introduced in
category theory. it's no way intended to be authoritive, neither really is it
meant to be pedagogical. it's basically my personal n-lab written in the exact
way that makes sense to my brain.

many times, i will have issues with the terminology used. i've been told that
this is not unusual. so wherever possible, i'll give a reference to the
'official' terminology while using my preferred words whenever possible.

as for the reason for my pedantry and unwillingness to settle for accepted
terminology, this is because i'm studying category theory in service of studying
type theory (HoTT in particular); as a result, common notions of `Set` are often
simply not rigorous enough for me to accept, because there's always the underlying
question of 'well why not use `Type`? or some other construction, and so on.

i am approaching this from a somewhat meta-theoretic perspective, and am not
completely married to type theory or whatever all consuming Latest Thing in
mathematics. my only real foundation is Frege's Sense and Reference.

if there were a thing that i'm somewhat married to, is the assumption of
intensionality by default. in other words, things don't have properties i
haven't explicitly given them. things are only "the same" with respect to
some previously defined property.

some words will not be defined as they are outside of the scope of category
theory. i'll leave outlinks to them whenever necessary. by convention, i'll
mark these words `between backticks`

================================================================================
part 1
================================================================================

# chapter 1: category: the essence of composition

__object__      : 
    a thing with no extra semantics. this might be polymorphic (as in, it may be
    used to describe higher order objects, like morphisms, or categories
    themselves, so disambiguation is necessary)
    used interchangeably with `thing` wherever it makes grammatical sense to do so,
    but semantically these two are the same thing (see what i did?)

__collection__  : 
    a loose container of things with no extra semantics.

__morphism__    :       denoted f (g, h, ... usually lower case letters)
    an arrow between objects. always directed.

__identity__    :       denoted id
    a specific morphism which maps an object to itself.

__unit__        :       denoted unit or ()
    a catchall word for an object with a special 'do-nothing' or 'trivial'
    property in some context. usually unique. common senses:
    - (type theory) the type with exactly one inhabitant
    - (category) terminal object: unique morphism into it from any object
    - (monoid/monad) identity element: x · unit = x = unit · x
    these are related: the terminal object in Set is a one-element set,
    which corresponds to the unit type.

__associative__ : 
    order of application doesn't matter. 
    a + b + c = (a + b) + c = a + (b + c)
    a degenerate case of
    [confluence](https://en.wikipedia.org/wiki/Church%E2%80%93Rosser_theorem)

__composition__ :
    connecting arrows together. if we have morphisms h g f, we can do
    h∘(g∘f) = (h∘g)∘f = h∘g∘f
    for morphisms, their composition is usually associative

__isomorphic__  :
    if two objects have morphisms to and from each other. losslessly.
    if i have objects A B, and morphisms f g in between them. then
    f g A = A and g f B = B
    in order words f g = id = g f. they're inverse.

__category__    :   denoted C (D, E, F ... basically captial letters)
    a collection of objects and morphisms such that every object has an
    identity morphism, and where composition of morphisms is associative.

--------------------------------------------------------------------------------

# chapter 2: types and functions

__set__ (object)    :
    informally, a collection of objects (if one is to use naive set theory).
    this works in most places, but not always. see Lawvere's theory for a proper
    treatment of set (the object) as it relates to Set (the category)

__Set__ (category)  :
    a category, whose objects are sets and morphisms are total functions
    between sets that has some extra structural properties. in particular,
    presence of:
    1. all (small) limits and colimits
    2. exponentials (function sets) (this means that Set is cartesian closed)
    3. a suboject classifier (making it a topos)
    notably, this is **not** the exact same `set` as is used in ZFC
    mathematics.

__set__ (ZFC)   :
    the set that people use in
    https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory

__type__        :
    can be thought of as a collection of objects, but has very notable semantics.
    in particular, the most important of which (and the thing that distinguishes
    it from sets) is that type membership is a `judgement` and not a `proposition`.
    in other words, it's an intrinsic statement as opposed to extrinsic. this is 
    true in almost all type systems and languages that use them.

__function__ (type) :
    is a morphism between types. internally, they do some stuff to inhabitants of
    those types. if it's a pure function, then these objects are `terms`.

__order__ (function):
    a function can be higher ordered if it itself takes in functions and or spits
    out functions (of varying orders). the converse for low-ordered functions.

__side effects__ (function) :
    a function has side effects if it does things that escape the local evaluation
    of an expression. like listening / outputting IO.

__pure__ (function) :
    a function is pure if it takes nothing but its input types and gives back
    nothing but its output types. no side effects allowed.

--------------------------------------------------------------------------------

# chapter 3: categories big and small

__free category__   :
    "thing that is at least not contradicting the definition of a category +
    stuff that would make it a category".
    think a simple directed graph + ids on every vertex.

__free construction__: 
    adding the minimal amount of components / structure to make thing X into
    thing Y.

__property__        :
    a judgement / predicate of an object that is either true (sometimes by
    construction) or false.

__binary operation__: 
    TODO  

__binary relation__: 
    TODO  

__reflexive__:
    TODO

__transitive__:
    TODO

__antisymmetric__:
    TODO

__equivalence relation__:
    it's a property. has some extra semantics if you're working with sets (i
    think)

__equivalence class__:
    all such objects (in some given context) that satisfies some property.
    as such, it doesn't make sense to just say 'here is an equivalence class',
    it only makes sense to say 'here is an equivalence class **with respect to**
    some property / equivalence relation.

__equivalent__      :
    two objects are equivalent (with respect to some equivalence relation R)
    if R holds between them.


__order__ (<,>,=,...):
    either refers to the generic concept of a an 'order between things' or
    a collection of objects equipped with an ordering relation (<, <=, ...)
    that may or may not have structural properties down the line.

__preorder__        :
    is a collection of objects equipped with an operator <= (read 'less than or
    equal to') that is `reflexive` and `transitive`.
    a <= a, a <= b and b <= c -> a <= c

__partial order__   :
    is a preorder, plus the extra property that <= must also be `antisymmetric`
    a <= b and b <= a -> a = b
    note: `=` here is very load bearing and specific use of it must be careful
    depending on context. sometimes it may just mean isomorphic, sometimes
    it means equivalent.

__equality__                : 
    specifically in the context of category theory, is almost always
    `propositional` / `extensional` equality, which means that two equal
    objects behave the same in all context. this can be thought of as a
    universal equivalence relation where the relation is question is
    everything you can express.

__monoid__ (set (zfc))      :
    a set equipped with a binary operation that is associative, and has an element
    that behaves like unit when applied to it.

__monoid__ (programming)    :
    is a design pattern for an interface for functions where you must implement
    two functions: return/id/mempty that is supposed to mimic identity, and 
    mappend that is supposed to be associative.
    ```haskell
    class Monoid m where
        mempty  :: m
        mappend :: m -> m -> m
    ```

__monoid__ (category)       :
    a category with a single object. usual semantics follow.

__hom__ (homomorphism)      :
    homomophisms from group theory are structure preserving maps. this is almost
    certainly not the thing that i'm referring to if i use the word Hom.

__hom-__ (category)         :
    a terribly overused and imprecise word used to describe 'a collection of
    things that are kinda like morphisms`.

__hom-set__                 : denoted C(A, B) or Hom_C(A, B)
    the collection of morphisms from object A to object B within category C.
    the word 'set' is historical baggage. may be a `hom-object` in `enriched`
    categories.

__Hom(C)__                  :
    all morphisms in category C. shorthand, less precise.

--------------------------------------------------------------------------------

# chapter 4: Kleisli categories

__kleisli category__        : denoted C_T or Kl(T)
    a category derived from a `monad` T on category C.
    - objects: same as C
    - morphisms A → B: morphisms A → T(B) in C (called "kleisli arrows")
    - identity: return (or η) : A → T(A)
    - composition: uses the monad's bind/extension to chain kleisli arrows
    the fish operator (>=>) is kleisli composition:
        (a -> T b) -> (b -> T c) -> (a -> T c)
    this is where "effectful functions" live as ordinary morphisms.

--------------------------------------------------------------------------------

# chapter 5: products and coproducts

__initial objects__
__terminal objects__
__dual__
__co-__
__products__
__coproducts__

--------------------------------------------------------------------------------

# chapter 6: simple algebraic data types

__product types__
__sum types__

--------------------------------------------------------------------------------

# chapter 7: functors

__functors__ (programming)
__functors__ (category)
__typeclass__ __interface__
__prerealizer__ __reader__
__functor laws__

--------------------------------------------------------------------------------

# chapter 8: functoriality

__bifunctors__
__universal property__
__universal construction__
__covariant__
__contravariant__
__covariant functor__
__contravariant functor__
__profunctor__
__hom-functor__

--------------------------------------------------------------------------------

# chapter 9: function types

__internal hom__
__external hom__
__currying__
__exponential__
__cartesian closed__
__cartesian closed categories__

--------------------------------------------------------------------------------

# chapter 10: natural transformations

__natural transformation__
__vertical composition__
__horizontal composition__
__naturality__
__n-category__

================================================================================
part 2
================================================================================

# chapter 1: declarative programming

--------------------------------------------------------------------------------

# chapter 2: limits and colimits

--------------------------------------------------------------------------------

# chapter 3: free monoids

--------------------------------------------------------------------------------

# chapter 4: representable functors

--------------------------------------------------------------------------------

# chapter 5: the yoneda lemma

--------------------------------------------------------------------------------

# chapter 6: yoneda embedding

================================================================================
part 3
================================================================================
