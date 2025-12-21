-- 1. show the isomophrism between Maybe a and Either () a

maybe2either : Maybe a -> Either () a
maybe2either m =
  case m of
    Just x  => Right x
    Nothing => Left ()

either2maybe : Either () a -> Maybe a
either2maybe e =
  case e of
    Left ()  => Nothing
    Right x  => Just x

------------------------------------------------------------

-- 2. Here’s a sum type defined in Haskell:
-- 
-- data Shape = Circle Float
--            | Rect Float Float
-- 
-- When we want to define a function like area that acts on a
-- Shape, we do it by pattern matching on the two constructors:
-- 
-- area :: Shape -> Float
-- area (Circle r) = pi * r * r
-- area (Rect d h) = d * h
-- 
-- Implement Shape in C++ or Java as an interface and create 
-- two classes: Circle and Rect. Implement area as a virtual function.

-- note: this is idris, so we'll do it natively

data Shape = Circle Double | Rect Double Double

area : Shape -> Double
area (Circle r) = pi * r * r
area (Rect w h) = w * h

------------------------------------------------------------

-- 3. Continuing with the previous example: We can easily 
-- add a new function circ that calculates the circumference 
-- of a Shape. We can do it without touching the definition of Shape:
-- 
-- circ :: Shape -> Float
-- circ (Circle r) = 2.0 * pi * r
-- circ (Rect d h) = 2.0 * (d + h)
-- 
-- Add circ to your C++ or Java implementation. What parts 
-- of the original code did you have to touch?

circ : Shape -> Double 
circ (Circle r) = 2.0 * pi * r
circ (Rect d h) = 2.0 * (d + h)


------------------------------------------------------------

-- 4. Continuing further: Add a new shape, Square, to Shape 
-- and make all the necessary updates. What code did you have 
-- to touch in Haskell vs. C++ or Java? (Even if you’re not 
-- a Haskell programmer, the modifications should be pretty obvious.)

data Shape' = Circle' Double | Rect' Double Double | Square' Double
area' : Shape' -> Double
area' (Circle' r) = pi * r * r
area' (Square' l) = l * l
area' (Rect' w h) = w * h

------------------------------------------------------------

-- 5. Show that a + a = 2 * a holds for types (up to isomorphism). 
-- Remember that 2 corresponds to Bool, according to our translation table.

sum2prod : Either a a -> (Bool, a)
sum2prod s =
  case s of
    Left a  => (False, a)
    Right a => (True, a)

prod2sum : (Bool, a) -> Either a a
prod2sum p =
  case p of
    (False, a) => Left a
    (True, a) => Right a


-- Proof that prodToSum is a left inverse of sumToProduct
leftInverse : (e : Either a a) -> prod2sum (sum2prod e) = e
leftInverse (Left x)  = Refl
leftInverse (Right x) = Refl

-- Proof that prodToSum is a right inverse of sumToProduct
rightInverse : (p : (Bool, a)) -> sum2prod (prod2sum p) = p
rightInverse (False, x) = Refl
rightInverse (True, x)  = Refl

record Iso a b where
  constructor MkIso
  to   : a -> b
  from : b -> a
  toFrom : (y : b) -> to (from y) = y
  fromTo : (x : a) -> from (to x) = x

eitherBoolIso : Iso (Either a a) (Bool, a)
eitherBoolIso = MkIso sum2prod prod2sum rightInverse leftInverse
