https://bartoszmilewski.com/2015/02/03/functoriality/


# text

## the writer funtor

```idris
Writer a = Pair a String
chain : (a -> Writer b) -> (b -> Writer c) -> (a -> Writer c)
chain m1 m2 = \x =>
  let (y, s1) = m1 x
      (z, s2) = m2 y
  in (z, s1 ++ s2)

return : a -> Writer a
return x = MkPair x ""

loggedAdd : Int -> Int -> Writer Int
loggedAdd x y = MkPair (x+y) ("added " ++ show x ++ " to " ++ show y ++ " ; ")

testWriter = chain (loggedAdd 1) (loggedAdd 2) 2
```


# challenges

1. Show that the data type:

```
data Pair a b = Pair a b
```

is a bifunctor. For additional credit implement all three methods of Bifunctor
and use equational reasoning to show that these definitions are compatible with
the default implementations whenever they can be applied.

```idris
data Pair' : Type -> Type -> Type where
  MkPair' : {0 a, b : Type} -> (x : a) -> (y : b) -> Pair' a b

Bifunctor Pair' where
  bimap f g (MkPair' a b) = MkPair' (f a) (g b)
  mapFst f (MkPair' a b) = MkPair' (f a) b
  mapSnd g (MkPair' a b) = MkPair' a (g b)

bimapIdEqId : (p: Pair' a b) -> bimap Prelude.id Prelude.id p = Prelude.id p
bimapIdEqId (MkPair' _ _) = Refl

bimapCompProof : (f : a -> a') -> (g : b -> b') ->
                 (f': a' -> a'') -> (g': b' -> b'') ->
                 (p : Pair' a b) ->
                 bimap (f' . f) (g' . g) p = bimap f' g' (bimap f g p)
bimapCompProof f g f' g' (MkPair' _ _) = Refl


mapFstCompat :  (f : a -> a') -> (p : Pair' a b) -> 
                mapFst f p = bimap f Prelude.id p 
mapFstCompat f (MkPair' _ _) = Refl

mapSndCompat :  (g : b -> b') -> (p : Pair' a b) -> 
                mapSnd g p = bimap Prelude.id g p 
mapSndCompat g (MkPair' _ _) = Refl
```

--------------------------------------------------------------------------------

2. Show the isomorphism between the standard definition of Maybe and this
   desugaring:

type Maybe' a = Either (Const () a) (Identity a)

Hint: Define two mappings between the two implementations. For additional
credit, show that they are the inverse of each other using equational
reasoning.

```idris
data Const : Type -> Type -> Type where
  MkConst : a -> Const a b

data Identity : Type -> Type where
  MkIdentity : a -> Identity a

Maybe' a = Either (Const () a) (Identity a)

maybe'2Maybe : Maybe' a -> Maybe a
maybe'2Maybe (Left a)               = Nothing
maybe'2Maybe (Right (MkIdentity a)) = Just a

maybe2Maybe' : Maybe a -> Maybe' a
maybe2Maybe' Nothing    = (Left (MkConst ()))
maybe2Maybe' (Just a)   = (Right (MkIdentity a))

maybe'Inv : (m : Maybe' a) -> (maybe2Maybe' $ maybe'2Maybe m) = m
maybe'Inv (Left (MkConst ()))       = Refl
maybe'Inv (Right (MkIdentity a))    = Refl

maybeInv  : (m : Maybe a)  -> (maybe'2Maybe $ maybe2Maybe' m) = m
maybeInv Nothing    = Refl
maybeInv (Just a)   = Refl
```

--------------------------------------------------------------------------------
3. Let’s try another data structure. I call it a PreList because it’s a
   precursor to a List. It replaces recursion with a type parameter b.

data PreList a b = Nil | Cons a b

You could recover our earlier definition of a List by recursively applying PreList to itself (we’ll see how it’s done when we talk about fixed points).

Show that PreList is an instance of Bifunctor.

```idris
data PreList a b = Nil | Cons a b

Bifunctor PreList where
  bimap f g Nil         = Nil
  bimap f g (Cons a b)  = Cons (f a) (g b)


bimapPreListIdEqId : (l : PreList a b) -> bimap Prelude.id Prelude.id l = l
bimapPreListIdEqId Nil          = Refl
bimapPreListIdEqId (Cons a b)   = Refl

bimapPreListCompProof : (f : a -> a') -> (g : b -> b') ->
                        (f': a' -> a'') -> (g': b' -> b'') ->
                        (p : PreList a b) 
  -> bimap (f' . f) (g' . g) p = bimap f' g' (bimap f g p)
bimapPreListCompProof f g f' g' Nil         = Refl
bimapPreListCompProof f g f' g' (Cons a b)  = Refl
```

--------------------------------------------------------------------------------
4. Show that the following data types define bifunctors in a and b:

data K2 c a b = K2 c

data Fst a b = Fst a

data Snd a b = Snd b

For additional credit, check your solutions agains Conor McBride’s paper Clowns
to the Left of me, Jokers to the Right.


```idris
data K2 c a b = MkK2 c

data Fst a b = MkFst a

data Snd a b = MkSnd b

Bifunctor (K2 c) where
  bimap f g (MkK2 z) = (MkK2 z)

Bifunctor Fst where
  bimap f g (MkFst a) = MkFst (f a)

Bifunctor Snd where
  bimap f g (MkSnd b) = MkSnd (g b)
```

it's quite tiresome to write out, but all three of these are valid
bifunctors, it just ignores some of the components. because it ignores
them, id will hold (id of nothing equals nothing), and composition
will hold too, since it composes normally on whatever arguments it didn't
ignore, and ignored everything else (f g Nothing = Nothing) so the
ignored clause doesn't matter.

--------------------------------------------------------------------------------

4. Define a bifunctor in a language other than Haskell. Implement bimap for a
   generic pair in that language.

see Challenge 1

--------------------------------------------------------------------------------

5. Should std::map be considered a bifunctor or a profunctor in the two
   template arguments Key and T? How would you redesign this data type to make
   it so?

not really, since the keys are fixed. so there's no notion in which it's
contravariant over them.

to make it so, you should redesign the datastructure s.t key transformations
are coherent. however, because transforming keys makes it so that you lose
information about the mapped to values, these key transformations would
themselves probably have to be functors.

but overall, the datastructure would have to be redesigned. does key <-> value
even form a coherent category given that the mapping function might use
a collision prone hashing function?
