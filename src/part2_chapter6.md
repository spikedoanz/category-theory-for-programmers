https://bartoszmilewski.com/2015/10/28/yoneda-embeddings/

0.  Extra credit: Express the Yoneda embeddings in idris
--------------------------------------------------------

```idris
btoa : Int -> String -- generically b -> a
btoa n = show n

fromY : forall x. (String -> x) -> (Int -> x)
fromY f b = f (btoa b)
```

1. Express the co-Yoneda embeddings in ~Haskell~ idris.
-------------------------------------------------------

if yoneda is

```
forall x. (a->x) -> (b->x) iso b -> a
```

then co-yoneda would be

```
forall x. (x->a) -> (x->b) iso a -> b
```

```idris
atob : a -> b

toY : forall x. (x->a) -> (x->b)
toY f a = (atob a) f

example_atob : Int -> String
example_atob a = show a

example_toY : forall x. (x->Int) -> (x->String)
example_toY f = example_atob . f
```

2. Show that the bijection we established between fromY and btoa is
   an isomorphism (the two mappings are the inverse of each other).
-------------------------------------------------------------------

```idris
phi : (forall x. (a -> x) -> (b -> x)) -> (b -> a)
phi nat = nat id

psi : (b -> a) -> (forall x. (a -> x) -> (b -> x))
psi f g = g . f

phipsi_id : phi (psi f) = f
phipsi_id = Refl

psiphi_id : {n : {x : Type} -> (a -> x) -> (b -> x)}  
            -> {y : Type}
            -> (g : a -> y)
            -> psi (phi n) g = n g
-- needs proof carrying natural transformations. will return later.
```

3. Work out the Yoneda embeddings for a monoid. What functor
   corresponds to the monoid’s single object? What natural
   transformations correspond to monoid morphisms?
------------------------------------------------------------

a monoid is a category M with one object * and morphisms m : * -> *

the yoneda embedding sends the object * to Hom(*,-) where - are the other
objects in the category. but since our category only has one object, - is
fixed to *.

so in fact, we send * to Hom(*,*), which is the set of morphisms in M

```
* |-> Hom(*,*)
```

in other words, the functor which corresponds to the monoid's single object is
```
Hom(*,-)() = Hom(*,*)
```

by yoneda, we have that

```
Nat(Hom(*,-), Hom(*,-)) iso Hom(*,*)
```

given f : * -> *, the corresponding natural transformation alpha has component:

alpha_*(-) = - o f

in otherwords, the corresponding natural transformation for the yoneda embedding
of a monoid is right composition with f.


4. What is the application of the covariant Yoneda embeddings to
   preorders? (Question suggested by Gershom Bazerman.)
----------------------------------------------------------------


5. Yoneda embeddings can be used to embed an arbitrary functor
   category [C, D] in the functor category [[C, D], Set]. Figure out
   how it works on morphisms (which in this case are natural
   transformations).
--------------------------------------------------------------
