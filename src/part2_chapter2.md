1. How would you describe a pushout in the category of C++ classes?

it's the diamond inheritance pattern. for the base A<-C->B, the pushout is the
object P which inherits from both A and B and is the minimal object to do so.
in other words, it's something that just inherits from both A and B.

--------------------------------------------------------------------------------

2. Show that the limit of the identity functor Id :: C -> C is the initial
   object.

Id creates a base that is every object in C, the only cone that could possibly
have all objects in C as a base are ones which have the initial object as the
apex. therefore, the limit of of the identity functor is the initial object.

--------------------------------------------------------------------------------

3. Subsets of a given set form a category. A morphism in that category is
   defined to be an arrow connecting two sets if the first is the subset of the
   second. What is a pullback of two sets in such a category? What’s a pushout?
   What are the initial and terminal objects?

the initial and terminal objects of the subset category would just be the empty
set and the set over which subsets are being taken itself.

the pullback pattern matches a base A->C<-B onto the subset category, which
sematically means bases are triples of subsets A B C, in which C is a larger
set that contains both A and B. our pullback an object P which is a subset of
both A and B, and is the largest object to do so (while still also being a
subset of C).

because the semantics of subset are transitive, this means that our pullback is
just our product, which means that P is just the intersection of A and
B.

the converse argument holds for the pushout, which means that our pushout is
the union of A and B.


--------------------------------------------------------------------------------

4. Can you guess what a coequalizer is?

an equalizer is the limit of a diagram D which maps from base J with two objects
{a,b} and morphisms {f,g} from a->b.

in a sense, what these cones express, is an extension of that morphism equality
between f=g, on the __left side__. the apex E has morphisms e1 and e2 (to a and
b respectively); s.t f o e1 = g o e1 and commutes with e2.

in this light, the coequalizer does the opposite: it extends the equality on
the right side.

note: in effect, e2 can be derived from the restriction that f o e1 and g o e1
commutes; but having it explicitly makes things a bit easier to think about in
my head.

--------------------------------------------------------------------------------

5. Show that, in a category with a terminal object, a pullback towards the
   terminal object is a product.

given:
    C: Category with terminal object T
    A, B: Objects in C
    
for the pullback:
    J1: Category {a, b, c} with morphisms {f: a→c, g: b→c}
    D1: J1 → C defined by D1(a)=A, D1(b)=B, D1(c)=T, 
        D1(f)=!_A, D1(g)=!_B  (the unique maps to T)

for the product:
    J2: Discrete category {a, b}
    D2: J2 → C defined by D2(a)=A, D2(b)=B

show:
    Lim D1 ≅ Lim D2


proof:
------

for the pullback, D1 is mapping a->A and b->B and c->T

the additional constraints in the universal property enforce that
the map D1(f) and D1(g) must map into T. however, because T is the terminal
object, we know that whatever f and g map into, they must be __the__ unique
morphisms that map A->T and B->T. therefore, these extra constraints are vacuous.

now, if we look at the remaining constraints of this pullback, we see that they
are the exact same constraints as the universal property of the product.

because these are universal constructions over the same category, the same
universal propeties will give us the exact same limit. therefore, Lim D1 ≅ Lim D2 


--------------------------------------------------------------------------------


6. Similarly, show that a pushout from an initial object (if one exists) is the
   coproduct.

invoking category theory, the proof in this instance is the exact same one as
in challenge 5, but with all of the arrows flipped.
