# Chapter 7 - Functors

Functor laws:
- Identity is preserved: `F id = id`
- Composition is preserved: `(h = g . f) -> (F h = F g . F f)`

## 1. Can we turn Maybe's constructor into a functor?

Can we define `fmap' _ _ = Nothing` which ignores both arguments? (Hint: check functor laws)

```idris
myFmap : (a -> b) -> Maybe a -> Maybe b
myFmap _ _ = Nothing

idLawNothing : myFmap Prelude.id Nothing = Prelude.id Nothing
idLawNothing = Refl

idLawViolation : Not (myFmap Prelude.id (Just ()) = Just ())
idLawViolation = uninhabited
```

Because the identity law doesn't hold, this can't be a valid functor.

## 2. Prove functor laws for Reader

```idris
reader : (a -> b) -> (r -> a) -> (r -> b)
reader f g = f . g

readerIdLaw : reader Prelude.id f = Prelude.id f
readerIdLaw = Refl

readerCompositionLaw : reader (g . f) x = (reader g . reader f) x
readerCompositionLaw = Refl

readerCompositionLaw' : reader (g . f) = reader g . reader f
readerCompositionLaw' = Refl
```

## 3. Implementation

The above is the implementation.

## 4. Prove functor laws for List functor

```idris
mapIdLaw : (xs : List a) -> map Prelude.id xs = xs
mapIdLaw [] = Refl
mapIdLaw (x :: xs) = cong (x ::) (mapIdLaw xs)

mapCompositionLaw : (xs : List a) -> map (g . f) xs = map g (map f (xs))
mapCompositionLaw [] = Refl
mapCompositionLaw (x :: xs) = cong (g (f (x)) ::) (mapCompositionLaw xs)
```
