1. Define a natural transformation from the Maybe functor to the list functor.
   Prove the naturality condition for it.

```idris
List2Maybe : List a -> Maybe a
List2Maybe Nil          = Nothing
List2Maybe (x :: xs)    = Just x -- don't think i can do anything with xs

List2MaybeNaturalConditionProof : 
  (f : a -> b) -> (xs : List a) -> map f (List2Maybe xs) = List2Maybe (map f xs)
List2MaybeNaturalConditionProof f [] = Refl
List2MaybeNaturalConditionProof f (x :: xs) = Refl
Maybe2List : Maybe a -> List a
Maybe2List Nothing  = Nil
Maybe2List (Just x) = x :: []

Maybe2ListNaturalConditionProof :
  (f : a -> b) -> (x : Maybe a) -> map f (Maybe2List x) = Maybe2List (map f x)
Maybe2ListNaturalConditionProof f Nothing   = Refl
Maybe2ListNaturalConditionProof f (Just x)  = Refl
```


--------------------------------------------------------------------------------

2. Define at least two different natural transformations between Reader () and
   the list functor. How many different lists of () are there?

```idris 
Reader : Type -> Type -> Type
Reader r a = r -> a

ReaderInitial2List : Reader () a -> List a
ReaderInitial2List f = [f ()]
```

regarding different lists of (), there's an infinite number of them. in fact
one for each Nat. thus, List () is isomorphic to Nat

--------------------------------------------------------------------------------
3. Continue the previous exercise with Reader Bool and Maybe.

```idris
ReaderBool2Maybe1 : Reader Bool a -> Maybe a
ReaderBool2Maybe1 f = Just (f True)

ReaderBool2Maybe2 : Reader Bool a -> Maybe a
ReaderBool2Maybe2 f = Just (f False)

ReaderBool2Maybe3 : Reader Bool a -> Maybe a
ReaderBool2Maybe3 f = Nothing
```

there should only be 3 of these

--------------------------------------------------------------------------------
4. Show that horizontal composition of natural transformation satisfies the
   naturality condition (hint: use components). It’s a good exercise in diagram
   chasing.

here's the algebraic proof

```
given:
  C D E : Categories
  a b : Objects
  f : a->b (polymorphic)
  F : Functor C->D
  F': Functor C->D
  G : Functor D->E
  G': Functor D->E
  \a: NaturalTransformation F->F'
  \b: NaturalTransformation G->G'
prove:
  G'F'f (\b\a)a = (\b\a)b GFf

we also have:
1. (\b\a)a = G'\aa \bFa
2. (\b\a)b = G'\ab \bFb
3. G'\aa \bFa = \bF'a G\aa by naturality square for \b
4. Gf \ba = \bb G'f by naturality of \b
5. F'f \aa = \ab Ff by naturality of \a

proof:
  G'F'f (\b\a)a = (\b\a)b GFf
------------------------------          rw [2]
  G'F'f (\b\a)a = (G'\ab \bFb) GFf
----------------------------------      rw [comp_trans]
  G'F'f (\b\a)a = G'\ab (\bFb GFf)
----------------------------------      rw [4]
  G'F'f (\b\a)a = G'\ab (G'Ff \bFa)
-----------------------------------     rw [comp_trans]
  G'F'f (\b\a)a = (G'\ab G'Ff) \bFa
-----------------------------------     rw [functoriality of G']
  G'F'f (\b\a)a = G'(\ab Ff) \bFa
---------------------------------       rw [<-5]
  G'F'f (\b\a)a = G'(F'f \aa) \bFa
----------------------------------      rw [<-functoriality of G']
  G'F'f (\b\a)a = (G'F'f G\aa) \bFa
----------------------------------      rw [comp_trans]
  G'F'f (\b\a)a = G'F'f (G\aa \bFa)
-----------------------------------     rw [<-1]
  G'F'f (\b\a)a = G'F'f (\b\a)a
-------------------------------         rfl
  T
```


the diagram proof

```
    G(F a) ----β_{F a}----> G'(F a) ----G'(αₐ)----> G'(F' a)
       |                       |                       |
 G(F f)|               G'(F f) |               G'(F' f)|
       |                       |                       |
       v                       v                       v
    G(F b) ----β_{F b}----> G'(F b) ----G'(α_b)----> G'(F' b)


                      glue the two squares


                G(F a) ----(β ∘ α)ₐ---> G'(F' a)
                   |                        |
            G(F f) |                        | G'(F' f)
                   |                        |
                   v                        v
                G(F b) ----(β ∘ α)_b---> G'(F' b)

                        this is the naturality
                        square for \b\a
          
```

--------------------------------------------------------------------------------
5. Write a short essay about how you may enjoy writing down the evident
   diagrams needed to prove the interchange law.

```
(β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)
```

https://discord.com/channels/1273109592359964763/1291496717803327558/1452788978930421800

i actually just did the thing. image attached.

lhs
(\b\a)      : GFa   -> GF'a     -> G'F'a    = GFa   -> G'F'a
(\b'\a')    : G'F'a -> G'F''a   -> G''F''a  = G'F'  -> G''F''a

rhs
(\a'\a)     : GFa   -> GF'a     -> GF''a    = GFa   -> GF''a
(\b'\b)     : GF''a -> G'F''a   -> G''F''a  = GF''a -> G''F''a

notice that these glue into the same thing

--------------------------------------------------------------------------------
6. Create a few test cases for the opposite naturality condition of
   transformations between different Op functors. Here’s one choice:

```haskell
op :: Op Bool Int
op = Op (\x -> x > 0)
```

and

```haskell
f :: String -> Int
f x = read x
```

```idris
record Op r a where
  constructor MkOp
  runOp : a -> r

interface Contravariant (f : Type -> Type) where
  contramap : (b -> a) -> f a -> f b

{r: Type} -> Contravariant (Op r) where
  contramap f (MkOp g) = MkOp (\x => g (f x))

predToStr : Op Bool a -> Op String a
predToStr (MkOp g) = MkOp (\x => if g x then "T" else "F")

op : Op Bool Int
op = MkOp (\x => x > 0)

f : String -> Int
f x = cast x

lhs = contramap f (predToStr op)
rhs = predToStr (contramap f op)

-- test with: runOp lhs "123" = runOp rhs "123"


op' : Op Int Bool
op' = MkOp (\x => if x then 42 else 0)

f' : Int -> Bool
f' x = (x == 42)


showOp : Op Int a -> Op Bool a
showOp (MkOp g) = MkOp (\x => g x == 42)

lhs' = contramap f' (showOp op')
rhs' = showOp (contramap f' op')

-- runOp lhs' 42 = runOp rhs' 42

```


