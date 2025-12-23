================================================================================
an extremely opinionated jargon file for category theory
================================================================================

this file serves as my working understanding of the terminology introduced in
category theory. it's no way intended to be authoritive, neither really
is it meant to be pedagogical. it's basically my personal n-lab written in
the exact way that makes sense to my brain.

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
theory. i'll leave outlinks to them whenever necessary.

================================================================================
part 1
================================================================================

# chapter 1: category: the essence of composition

__object__      : 
    a thing with no extra semantics. this might be polymorphic (as in, it may be
    used to describe higher order objects, like morphisms, or categories
    themselves, so disambiguation is necessary)

__collection__  : 
    a loose container of things with no extra semantics.

__morphism__    : 
    an arrow between objects. always directed.

__identity__    :
    a specific morphism which maps an object to itself. abbreviated as `id`

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

__category__    :
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

__type__        :
    can be thought of as a collection of objects, but has very notable semantics.
    in particular, the most important of which (and the thing that distinguishes
    it from sets) is that type membership is a `judgement` and not a `proposition`.
    in other words, it's an intrinsic statement as opposed to extrinsic. this is 
    true in almost all type systems and languages that use them.

__
