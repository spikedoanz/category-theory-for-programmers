https://bartoszmilewski.com/2015/07/29/representable-functors/

1. Show that the hom-functors map identity morphisms in C to corresponding
   identity functions in Set.

a. Hom(A,-), the covariant version, given a morphism f:x->x', has an induced
map Hom(A,f): Hom(A,x) -> Hom(A,x') defined as g |-> f g

if f is Id, Hom(A,Id) sends g |-> Id g = g

this means that, for the covariant hom-functor the induced map of the Id
morphism is the identity function on the set Hom(A,x)

b. Hom(-,B), the contravariant version, given a morphism f:x->x', has an
induced map Hom(f,B): Hom(x',B) -> Hom(x,B). the direction is backwards in this
case because otherwise it can't be composed with f.

this one is defined as g |-> g f

if f is Id, Hom(Id, B) sends g |-> g id = g

this means that, for the contravariant hom-functor, the induced map of the Id
morphism is the identity function on the set Hom(x,B)

--------------------------------------------------------------------------------

2. Show that Maybe is not representable.

as a functor, Maybe is an endofunctor with the signature : C->C, defined by
- on objects: Maybe(A) = A + 1 (1 in this case is Nothing)
- on morphisms: Maybe(f) = f + id (f to Just, id to 1)

to be representable, Maybe would have to be naturally isomorphic to the
hom-functor from C->Set at some object A.

Maybe(-) ≅ Hom(A, −) (a)

we evaluate (a) at 1, the 'nothing' case

|Maybe(1)| has cardinality 1 + 1 = 2 (Just Nothing and Nothing)
|Hom(A,1)| has only 1, since it's the terminal object and thus has only one
unique morphism from A to it forall A.

--------------------------------------------------------------------------------

3. Is the Reader functor representable?

reader itself is isomorphic to the function type, in face, it literally
is the constructor for a function type, with nothing more and less.

as such, it is exactly Hom(r,a), which is isomorphic to Hom(r,a). waow!

--------------------------------------------------------------------------------

4. Using Stream representation, memoize a function that squares its argument.

```idris
-- interface Functor f => Representable (f : Type -> Type) where
--   Rep : Type
--   tabulate : (Rep -> a) -> f a
--   index : f a -> Rep -> a
-- 
-- Representable Stream where
--   Rep = Nat
--   tabulate f = f 0 :: tabulate (f . S)
--   index (x :: _)    Z       = x
--   index (_ :: xs)   (S n)   = index xs n
-- 
-- squares : Stream Nat
-- squares = tabulate (\n => n*n)
-- 
-- memoizedSquares : Nat -> Nat
-- memoizedSquares n = index squares n

```

--------------------------------------------------------------------------------


5. Show that tabulate and index for Stream are indeed the inverse of each
   other. (Hint: use induction.)

```idris
interface Functor f => Representable (f : Type -> Type) where
  Rep : Type
  tabulate : (Rep -> a) -> f a
  index : f a -> Rep -> a

Representable Stream where
  Rep = Nat
  tabulate f = f 0 :: tabulate (\x => f (S x))
  index (x :: _)    Z       = x
  index (_ :: xs)   (S n)   = index xs n

-- all three of these hang
idProof : (f: Nat -> Nat) -> (n : Nat) -> index (tabulate f {f = Stream}) n = f n
idProof f Z     = Refl
-- idProof f (S k) = idProof (f . S) k
-- idProof f (S k) = rewrite sym (idProof (f . S) k) in Refl
idProof f (S k) = idProof (\m => f (S m)) k
```

6. The functor:

Pair a = Pair a a

is representable. Can you guess the type that represents it? Implement tabulate
and index.

```idris
data Pair' a = MkPair a a

Functor Pair' where
  map f (MkPair x y) = MkPair (f x) (f y)

Representable Pair' where
  Rep = Bool
  tabulate f = MkPair (f False) (f True)
  index (MkPair x _) False  = x
  index (MkPair _ y) True   = y
```
