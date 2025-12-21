-- functor laws:
-- id is preserved : F id = id
-- composition is preserved : (h = g . f) -> (F h = F g . F f)


-- 1. can we turn Maybe's constructor into a functor by defining
-- fmap' _ _ = Nothing
-- which ignores both arguments (hint: check functor laws)


myFmap : (a -> b) -> Maybe a -> Maybe b
myFmap _ _ = Nothing

idLawNothing : myFmap Prelude.id Nothing = Prelude.id Nothing
idLawNothing = Refl

idLawViolation : Not (myFmap Prelude.id (Just ()) = Just ())
idLawViolation = uninhabited

-- because the identity law doesn't hold, this can't be a valid functor


-- 2. prove functor laws for reader

reader : (a -> b) -> (r -> a) -> (r -> b)
reader f g = f . g

readerIdLaw : reader Prelude.id f = Prelude.id f
readerIdLaw = Refl

readerCompositionLaw : reader (g . f) x = (reader g . reader f) x
readerCompositionLaw = Refl

readerCompositionLaw' : reader (g . f) = reader g . reader f
readerCompositionLaw' = Refl

-- 3. the above is the implementation

-- 4. prove functor laws for list functor

mapIdLaw : (xs : List a) -> map Prelude.id xs = xs
mapIdLaw [] = Refl
mapIdLaw (x :: xs) = cong (x ::) (mapIdLaw xs) 

mapCompositionLaw : (xs : List a) -> map (g . f) xs = map g (map f (xs))
mapCompositionLaw [] = Refl
mapCompositionLaw (x :: xs) = cong (g (f (x)) ::) (mapCompositionLaw xs)
