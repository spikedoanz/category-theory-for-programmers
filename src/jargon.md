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
    category theory isn't usually thought of as an intensional theory, but
    in reality, because everything requires either an explicit existence of
    a given morphism / construction, in effect is has judgemental semantics.

__binary operation__: 
    a binary operation +/*/... takes two arguments and spits one thing out

__binary relation__:
    a binary relation R between objects A and B holds if A is related to B in
    some way. this 'way' is defined by the semantics of the relation in question,
    such as ordering, morphisms, ...

__reflexive__:
    a binary relation is reflexive if the relation R relates every object A to itself.

__transitive__:
    a binary relation R is reflexive if for all objects A B C
    A R B and B R C implies A R C

__antisymmetric__:
    a binary relation R is antisymmetric if forall objects A B
    A R B and B R A implies A '=' B
    note: as always 'equality' here is extremely load bearing and often will
    not be true in practice. especially in category theory where equality
    isn't a great topic of discussion. it's usually better to think of
    isomorphism in our context.

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

__initial objects__ :
    an initial object has an unique morphism from it to every object in the
    category. this includes itself, for which the morphism is Id.

__terminal objects__:
    a terminal object has has an unique morphism from every object in the
    category to it. including itself, which is Id, etc etc.
    note: for both terminal and initial objects, because the associated
    morphisms are unique, we can `identify` all of the objects in the category
    by the morphisms they have to/from its initial/terminal objects. identify
    here is used a bit loosely, but know that it is not as strict as isomophism.

__dual__            :
    a construction in category theory is dual to another if the directionality of
    all morphisms are reversed.

__co-__             :
    alias for the dual of a construction. product is dual to coproduct ... 

__products__        :
    for two objects A and B, a product consists of
    1. the object C: A x B
    2. two projection morphisms p1 and p2 from C to A and B respectively
        note: these morphisms are also somtimes called 'left' and 'right'
    which satisfies the [universal property`: for any object C' with
    morphisms 
        f: C->A and g: C->B s.t
        p1 o (f, g) = f
        p2 o (f, g) = g
    in other words, the product is the `most general` object that maps
    into both A and B.

__coproducts__      :
    the dual of product, consists of
    1. the object A + B
    2. two injective morphisms i1: A -> A+B and i2: B ->A+B
    satisfying the universal propertytwo morphisms f: A+B -> A and g: A+B -> B
    such that there exists a **unique** morphism [f,g]: A+B -> C
    such that [f,g] o i1 = f and [f,g] o i2 = g

--------------------------------------------------------------------------------

# chapter 6: simple algebraic data types

__product types__
```idris
product = Pair Int String
-- though i would prefer if this was called 'Both'
```

__sum types__
```idris
coproduct = Either Int String
```
        

--------------------------------------------------------------------------------

# chapter 7: functors

__functors__ (programming)
    ```
    Main> :doc Functor
    interface Prelude.Functor : (Type -> Type) -> Type
      Functors allow a uniform action over a parameterised type.
      @ f a parameterised type
      Parameters: f
      Constructor: MkFunctor
      Methods:
        map : (a -> b) -> f a -> f b
          Apply a function across everything of type 'a' in a parameterised type
          @ f the parameterised type
          @ func the function to apply
    ```

    
__functors__ (category)     :
    functors map categories to categories (objects -> objects and morphisms to
    morphisms) in such a way that, for a given functor F
    1. identity is preserved: F id = id
    2. composition is preserved: F (g o f) = F g o F f

__interface__ __typeclass__ 
    is a way of enforcing ccertain api are available. for instance (heh),
    things that are of instance Functor must implement a 'map' function.
    haskell calls these typeclasses, but i prefer interface.

__prerealizer__ __reader__
    https://hackage-content.haskell.org/package/mtl-2.3.2/docs/Control-Monad-Reader.html
    basically takes in a function, and returns something that you can manually
    invoke to actually execute that function.
```idris
record Prerealizer (r : Type) (a : Type) where
    constructor MkPrerealizer
    realize : r -> a

Functor (Prerealizer r) where
    map f (MkPrerealizer g) = MkPrerealizer (f . g)
```
     
__functor laws__
    1. identity is preserved: F id = id
    2. composition is preserved: F (g o f) = F g o F f

--------------------------------------------------------------------------------

# chapter 8: functoriality

__bifunctors__
    bifunctors are functors which map two categories into one category.

__universal property__
    is a way of constructing a new category s.t it gives us a desired *property*,
    for which the thing that is *universal* are either the terminal or initial
    objects in that category.
    degenerate example: the inital and terminal objects of any category C can be
    defined by first constructing a new category C' from C by applying id to
    everything, and then finding the initial and terminal objects of C'
    less degenerate example: from a category C, we construct a new category C'
    where:
    1. objects are triples (X, X->a, X->b) an object X with projection functions
    to any two objects a and b.
    2. morphisms are maps from X -> Y (both X and Y are objects in C)
    the actual **product** is the one that is the 'most general' among these
    categories. in our case because we want the construction that is the
    'tighest' (only has morphisms from X to X,a,b, we choose the terminal
    object in C'.
    objects satisfying the universal property are unique up to isomorphism, but this
    is a collolary of the fact that they're terminal/initial objects in C'.

__universal construction__
    the process done in the example in [universal property] produces a universal
    construction for a given universal property. many objects are defined through
    this process; such as products, coproducts, and eventually the yoneda embedding.
    
__covariant__
    'in the same direcdtion' : (a -> b) -> (a -> b)

__contravariant__
    'in the opposite direction' (a -> b) -> (b -> a)

__covariant functor__
    is one that doesn't flip the order of morphisms.

__contravariant functor__
    is one that does flip the order of morphisms. 

__profunctor__
    is a special case of a bifunctor which is contravariant in the first argument
    and covariant in the second.
    (c -> a) -> (b -> d) -> f a b -> f c d

__hom-functor__ :   denoted Hom(-,-): C^op x C -> Set
    given objects a and b, it returns the collect of morphisms Hom(a,b). it
    behaves like an identity on profunctor composition, (which is defined via
    `coends`, not ordinary functor composition).

--------------------------------------------------------------------------------

# chapter 9: function types

__exponential__
    is defined by a universal construction. take category C with arbitrary objects
    a and b, we construct a new category C' with:
    1. objects (X, f: X x a -> b)
    2. morphisms are maps X -> y
    the exponential is the terminal object in this category.
    given that you need X x a to define the exponential, it's obvious to see
    that a category must have a product in order to have an exponential.
    (a -> b, or [a,b]) is usually denoted B^A
    a different perspective is that exponentials are `right adjoint` to products
    Hom(X x a, b) ≅ Hom(X, b^a)


__internal hom__
    is a bad word. just use [exponential] instead.

__external hom__
    is the collection of morphisms from any objects a and b in some category C,
    this always exists. the duality between external and internal homs aren't
    dual in any useful way, so it's better to just call external homs
    `the collection of morhpisms from a to b' denoted 'Hom(a,b)' or C(a,b) instead

__currying__
    is the process of turning products into exponentials using the right
    adjuction identity.
    a x b -> c
    ---------- curry
    a -> b -> c

__uncurrying__
    does the opposite of currying, turns exponentials into products. do be careful
    since exponentials are right associative. a -> b -> c means a -> (b -> c), not
    (a -> b) -> c
    a -> b -> c
    ------------ uncurry
    a x b -> c

__cartesian closed__
    a category is cartesian closed if it has
    1. a terminal object
    2. all binary products
    3. exponentials of all pairs of objects
    this word applies to things that aren't necessarily categories. such as preorders.
    preorders which are cartesian closed are called `heyting algebras`. it's almost
    a lattice, if you don't enforce antisymmetry through partial orders.
    

--------------------------------------------------------------------------------

# chapter 10: natural transformations

__natural transformation__
    a natural transformation is a morphism between functors.
    categories C, D; functors F, G: C->D. the natural transformation is
    alpha_a : F(a) -> G(a) for any object a in C s.t forall morphisms
    f : a -> b in C
    G(f) o alpha_a = alpha_b o F (f)
    the above identity is called the `naturality square`

__naturality__
    the condition that makes a transformation "natural" -- the square above
    commutes for all f. informally: the transformation doesn't depend on the
    specific object, it works uniformly across the whole category.

__vertical composition__
    given natural transformations alpha: F => G and beta: G => H (same source
    and target categories), compose component-wise:
    (beta . alpha)_a = beta_a o alpha_a
    this is just ordinary morphism composition at each object.

__horizontal composition__
    given alpha: F => G (functors C -> D) and beta: H => K (functors D -> E),
    horizontal composition gives (beta * alpha): H o F => K o G.
    mixes functor composition with natural transformations. interchanges
    with vertical composition (interchange law).

__n-category__
    a category with morphisms between morphisms, up to n levels.
    0-category: a set (objects only)
    1-category: ordinary category (objects, morphisms)
    2-category: has 2-morphisms between morphisms (natural transformations)
    and so on. vertical and horizontal composition live here.

================================================================================
part 2
================================================================================

# chapter 1: declarative programming

--------------------------------------------------------------------------------

# chapter 2: limits and colimits


__index category__
    is a category whose job is to draw out a desired diagram to be projected onto
    a different category. for products, J would be the category 2, with two
    objects and no morphism besides id.

__diagram__ : denoted D: J → C
    a functor from an index category J into C. picks out a "shape" of objects
    and morphisms in C.

__cone__
    ingredients:
    1. a source category C
    2. an index category J
    3. a functor D (called the diagram) : J -> C
    when we apply D, the cone is an **apex** N in C with morphisms N->D(j)
    forall j (indeces), commuting with D. alternatively, we can also use a
    constant functor \Delta_c, which maps all indices in J to a single object in
    C (our desired apex). the natural transformation from \Delta_c to D exactly
    gives us a category of cones.
    note that \Delta_c is not a single functor, but a whole family of them,
    representing **all** of the ways to get an apex from J to some object
    in C.

__limit__
    is the terminal cone of a diagram. in other words, it's the universal
    construction which satisfies the property: being a cone, and don't have 
    any morhpisms from your apex to another cone's apex. in my head i imagine
    the limit to be the cone that is 'closest' to the category. all of the
    other cones are taller, because of that extra morphism from their apex
    to the limit's apex.

__cocone__
    does the exact opposite to the same diagram D : J -> C
    the cocone has an apex N in C with morphisms D(j) -> N.
    i imagine a pyamid digging into the ground.

__colimit__
    the initial object among cocones. it's also the closest to the category.
    all of the other cocones are further away from the colimit, because there
    is an extra morphism going from the colimit's apex to the other cocones'
    apex.


--------------------------------------------------------------------------------

# chapter 3: free monoids

__generators__
  a collection of objects with no structure. the input to a 
  [free construction]. concretely: the alphabet we perform `kleene` star
  over. abstractly: in the universal construction, this collection is treated
  as an object x in Set, embedded into structures via functions 
  `p :: x -> U m` where
  - U is a forgetful functor from the target category to Set
  - m is the constructed object

__free monoid__
  the monoid generated by performing kleene star over a collection of
  generators. multiplication is concatenation, unit is the empty list.
  ~    
  quotiented only by the equivalences required by monoid laws:
  - (a, e) ~ a ~ (e, a)         (unit)
  - (a, (b, c)) ~ ((a, b), c)   (associativity)
  ~
  other monoids are quotients of free monoids by additional equivalences.
  e.g., integers under multiplication quotient by commutativity 
  ((a, b) ~ (b, a)) and by the multiplication relation itself 
  ([2, 3] ~ [6]).
  ~
  other monoids are quotients of free monoids by additional equivalences.
  abstractly: the initial object in the category where
  - objects are pairs (m, p) with m a monoid and p :: x -> U m
  - morphisms are homomorphisms h :: m -> n such that q = U h . p
  ~
  the unique homomorphism h from the free monoid to any other monoid
  witnesses the quotient—it collapses equivalence classes.

__Mon__ (category)
  the category where
  - objects are monoids: triples (S, ·, e) where S is a set, · is an
    associative binary operation on S, and e ∈ S is the unit
  - morphisms are homomorphisms: functions h : S -> S' such that
    h(a · b) = h(a) · h(b) and h(e) = e'
  ~
  e.g., (ℤ, *, 1), (ℕ, +, 0), (List a, ++, [])

__homomorphism__ (monoid)
  a morphism in Mon. a function h between monoids that preserves structure:
  - h(a · b) = h(a) · h(b)     (preserves multiplication)
  - h(e) = e'                   (preserves unit)
  ~
  e.g., h : (List ℕ, ++, []) -> (ℕ, *, 1) defined by
  - h([n]) = n
  - h([2, 3]) = h([2]) * h([3]) = 6
  - h([]) = 1
  ~
  the homomorphism from a free monoid to any other monoid witnesses a
  quotient -- it collapses equivalence classes.

__forgetful functor__
  a functor U : C -> Set that "forgets" structure.
  ~
  e.g., U : Mon -> Set
  - on objects: sends (ℤ, *, 1) to ℤ
  - on morphisms: sends a homomorphism h to the same function, forgetting
  that it preserves multiplication and unit
  the left adjoint to a forgetful functor (when it exists) is the
  corresponding free functor. see [adjunction].

__underlying set__
  U m where U is a forgetful functor, and m is a monoid
  ~
  e.g., the underlying set of (ℤ, *, 1) is ℤ.


--------------------------------------------------------------------------------

# chapter 4: representable functors

--------------------------------------------------------------------------------

# chapter 5: the yoneda lemma

--------------------------------------------------------------------------------

# chapter 6: yoneda embedding

================================================================================
part 3
================================================================================
