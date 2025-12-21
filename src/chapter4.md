1. show that the terminal object is unique up to unique isomorphism

equivalently: this says that: forall terminal objects x of a category, there
exists a terminal object y such that it satisfies the same "one arrow from
every object" criteria, s.t (y and x are not uniquely isomorphic) -> bottom

proof: given that terminal objects y have exactly one arrow going into it
from all objects in the category, including all the terminal objects x, this
gives us a unique morphism x -> y. 

we also consider that since all objects x are also terminal objects, that
they have a single morphism going from every object into it, including y.
this means that forall terminal objects x we a unique morphism y -> x.

since we have forall x, there is a unique morphism x -> y and y -> x; we can
now construct the morphism x -> y -> x by chaining these. thus obtaining a
morphism from x -> x. however, since there is only one morphism from x -> x,
id, we conclude that x -> y -> x must be the same as id. ditto for y -> x -> y.
therefore y and x are isomorphic.

--------------------------------------------------------------------------------

2. what is the product of two objects in a poset? hint: use the universal
   construction

a poset consists of objects {x1, x2,...xn}, equipped with a reflexive, transitive
operator <= that is

a. reflexive a <= a
b. transitive a <= b ; b <= c -> a <= c
c. antisymmetric a <= b ; b <= a -> a = b

the product of two objects (a x b) should satisfy:

1. (a x b) <= a
2. (a x b) <= b
3. forall c , c <= a and c <= b -> c <= (a x b)
4. all objects satisfying 1-3 are uniquely isomorphic

proof of (4): assume we have an object d, that is:
a. d <= a
b. d <= b
c. forall c, c <= a and c <= b -> c <= d

we specialize c to become (a x b), then we have

e. (a x b) <= d

in (3), we specialize c to be d, then we have

f. d <= (a x b)

compose e and f together, we get d <= (a x b) <= d -> d <= d,               which is id
compose f and e together, we get (a x b) <= d <= (a x b) -> a x b <= a x b, which is id

therefore, these two must be isomorphic

--------------------------------------------------------------------------------

3. what is the coproduct of two objects in a poset

the coproduct of two objects (a + b) should satisfy:

1. a <= a + b
2. b <= a + b
3. forall c, a <= c and b <= c -> a + b <= c
4. all objects satisfying 1-3 are uniquely isomorphic 

proof of (4): assume we have an object d, that is

a. a <= d
b. b <= d
c. forall c, a <= c and b <= c -> d <= c

in (c), we specialize c to be a + b

d. a <= a + b and b <= a + b -> d <= a + b

both of these conjuctive clauses are true by apply 1 and 2, thus we have

e. d <= a + b

in (3), we specialize c to be d. we then apply the same argument as d -> e

f. a + b <= d

compose e f, we get d <= d = id
compose f e, we get a + b <= a + b = id

qed


--------------------------------------------------------------------------------

4. Implement the equivalent of Haskell Either as a generic type in your
   favorite language (other than Haskell).

```idris
data Either' a b = Left a | Right b
```

--------------------------------------------------------------------------------

5. Show that Either' is a “better” coproduct than int equipped with two injections: 

```idris

int2int : Int -> Int
int2int n = n

bool2int : Bool -> Int
bool2int b = if b then 0 else 1
```

to be a good coproduct, forall types a, b, (or specificallly Int and Bool in
the case of `int`), we need our coproduct c to satisfy
1. a -> c
2. b -> c
3. forall c', (a -> c' and b -> c') -> c -> c'
4. that all instances of c are uniquely isomorphic

for Either', we have

1. a -> Either' a b = Left a
2. b -> Either' a b = Right b
proof of (3):

we call functions of a -> c' = f
we call functions of b -> c' = g

we can construct the function c -> c' as such

```idris
Either'map : (a -> c') -> (b -> c') -> (Either a b -> c')
Either'map f g c =
  case c of
    Left a => f a
    Right b => g b
```

4. given any coproduct C with injections i, j we construct morphisms in both
   directions:

```idris
either2c : (i : a -> c) -> (j : b -> c) -> Either' a b -> c
either2c i j (Left a) = i a
either2c i j (Right b) = j b

c2either : {a, b, c : Type} -> (factorizer : {x : Type} -> (a -> x) -> (b -> x) -> c -> x) -> c -> Either' a b
c2either factor = factor {x = Either' a b} Left Right
```

Id is unique on both sides, so this is an isomophism

5. to show that Either' is 'better' than int, we need to show that for all
   morphisms i, j from Int|Bool -> Int, there is a morphisms m : Either' Int Bool -> int
   that factorizes the injections
   i = m . Left
   j = m . Right
   to make Either' strictly better, we need to make it so that the inverse
   situation: a morphism m' : int -> Either' Int Bool. doesn't exist

```idris
Either'2int : Either Int Bool -> Int
Either'2int c = case c of
  Left a  => int2int a
  Right b => bool2int b
```

however, when we try to do the opposite, we get an issue:

```idris
int2Either' : Int -> Either Int Bool
int2Either' i = case i of
  0 => Right False -- how do we know if we should shove this into Left or Right?
  1 => Right True  -- ditto
  i' => Left i'
```

since we can't tell which of the Int constructors to choose, this means that
there are __more__ than one morphisms from Int -> Int | Bool, thus making this not
a valid coproduct.

--------------------------------------------------------------------------------

6. Continuing the previous problem: How would you argue that int with the two
   injections i and j cannot be “better” than Either?

already did:
> since we can't tell which of the Int constructors to choose, this means that
> there are __more__ than one morphisms from Int -> Int | Bool, thus making this not
> a valid coproduct.

--------------------------------------------------------------------------------

7. Still continuing: What about these injections? 

```c
int i(int n) { 
    if (n < 0) return n; 
    return n + 2;
}
int j(bool b) { return b? 0: 1; }
```

this one would work, because the domain of the ints are now (-inf, -1] union
[2, inf) and the domain for the bool is now [0,1]. since these are disjoint,
we can actually create an unique isomophrism


```idris
betterInt2Either' : Int -> Either Int Bool
betterInt2Either' i = case i of
  0 => Right False
  1 => Right True
  i' => if (i' < 0) then Left i' else Left (i' - 2)
```

--------------------------------------------------------------------------------

8. Come up with an inferior candidate for a coproduct of int and bool that
   cannot be better than Either because it allows multiple acceptable morphisms
   from it to Either.

trivial example, just flip 0 and 1 in the bool args.
