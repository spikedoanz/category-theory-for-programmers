https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/

0. Extra credit (by me):
Prove the Yoneda lemma

```
have:
  C         : Category
  F         : Functor (arbitrary)
  a         : Object in C
  C(a,-)    : Hom-functor / Presheaf
              this is both for objects C(a,x) and morphisms C(a,-)(f)
  Nat       : Natural transformation
              otherwise read as alpha_x : C(a,x) -> F(x) forall x
prove
  Nat(C(a,-),F(-)) ≅ F a

proof sketch:
    define p
        |
        V
    naturality square at a --> equation (*)
        |                           │
        |                           V
        |                     full square -> (*1)
        |                           -
        V                           V
    define phi                  define psi (needs (*1) for well-definedness)
        |                           |
        |-----------|---------------|
        V           V               
      phipsi = id   psiphi= id (needs naturality again)
        |           |
        V           V
        isomorphism
            |
        |-------|
        V       V
     nat in F   nat in a (needs (*2))

proof:

let p := alpha_a id_a, which is in F(a)
let g : a -> x
we consider the naturality square if we set - = a

  C(a,a) --- C(a,-)(g) ---> C(a,x)
    |                         |
    |                         |
  alpha_a                 alpha_x
    |                         |
    V                         V
  F(a) ----- F(g) ------>   F(x) 

rw [C(a,a) = id_a]

  id_a   --- C(a,-)(g) --->    g
    |                       |
    |                       |
  alpha_a               alpha_x
    |                       |
    V                       V
    p ----- F(g) ------> F(g)(p) = alpha_x g

since the right side is a constant for a fixed a, we have that
forall g: a -> x, forall x
alpha_x g = F(g)(p) (*)

we draw the full naturality square 

  C(a,x) --- C(a,-)(f) ---> C(a,y)
    |                       |
    |                       |
  alpha_x               alpha_y
    |                       |
    V                       V
  F(x) ----- F(f) ------> F(y) 

rw C(a,x) for arbitrary g : a -> x
rw C(a,y) for application of C(a,-)(f) to C(a,x)

    g       --- C(a,-)(f)  --->    f g
    |                            |
    |                            |
  alpha_x                    alpha_y
    |                            |
    V                            V
 alpha_x g  ----- F(f) ------>  ???

going right, then down, we obtain

alpha_y (f g)
------------- rw [*] where f g : a -> y
F(f g)(p)
--------- rw [functor laws for F]
F(f) F(g) (p)

going down, then right, we obtain

F(f) alpha_x g
-------------- rw [*] where g : a -> x
F(f) F(g) (p)

therefore, the full naturality square for alpha commutes (*1)

let psi(p) := alpha  where  alpha_x (g) = F(g)(p)
we know from (*1) that alpha commutes, so ψ(p) is also natural
let phi(alpha) := alpha_a (id_a)

now we show that 

phi(psi(p)) = id p 
---------------- rw [definition of psi]
phi(alpha) = id p
----------------- rw [definition of phi]
alpha_a (id_a) = id p
--------------------- rw [definition of p]
alpha_a (id_a) = id alpha_a (id_a)
---------------------------------- rw [apply id]
alpha_a (id_a) = alpha_a (id_a)
------------------------------- refl
[]


we also need to show that
psi(phi(alpha)) = id alpha
------------------------- rw [definition of phi]
psi(alpha_a (id_a)) = id alpha
------------------------------ rw [definition of psi]
beta = alpha                    -- where beta_x (g) = F(g)(alpha_a(id_a))

we need to show that
forall x
forall g: a->x
beta_x(g) = alpha_x(g)
---------------------- rw [definition of beta]
F(g)(alpha_a(id_a)) = alpha_x(g)

consider the naturality square for C(a,a), C(a,x)

  C(a,a) --- C(a,-)(g) ---> C(a,x)
    |                       |
    |                       |
  alpha_a               alpha_x
    |                       |
    V                       V
  F(a) ----- F(g) ------> F(x) 

rw [uniqueness of id C(a,a)]

   id ------------- C(a,-)(g) -----> g
    |                                |
    |                                |
  alpha_a                        alpha_x
    |                                |
    V                                V
  alpha_a (id_a) ----- F(g) ------> alpha_x (g) / F(g) alpha_a (id_a)

alpha is natural, so this commutes, therefore

alpha_x(g) = F(g) (alpha_a(id_a))

therefore
  beta = alpha

therefore
  psi(phi(alpha)) = alpha = id alpha
------------------------------------ refl
[]

we have proven the yoneda lemma for a fixed object a and fixed functor F


to prove that the yoneda lemma is natural in F, we need to show that
forall natural transformations beta from F to an arbitrary functor G, beta is natural.


  Nat(C(a,-), F) --- phi --- > F(a)
      |                             |
      |                             |
  beta_-                        beta_a
      |                             |
      V                             V
  Nat(C(a,-),G) --- phi --- > G(a)


going right down, we get : Nat(C(a,-), F) |-> phi (Nat(C(a,-), F)) = alpha_a (id_a) |-> beta_a (alpha_a (id_a))
going down right, we get : Nat(C(a,-), F) |-> beta alpha         |-> phi (beta alpha) = beta_a (alpha_a (id_a))

by refl, these are equal, which shows that beta satisfies the naturality conditions.

we also need to prove that the yoneda lemma is natural in a, which means showing that
forall b
forall f: b -> a
let alpha := Nat(C(b,-),F)

note: C(f,-)_a : C(b,b) -> C(b, a)

the following square commutes:
  
  alpha         --- phi --->  F(b)
    |                             |
    |                             |
  - o C(f,-)                     F(f)
    |                             |
    V                             V
  Nat(C(a,-),F) --- phi ---> F(a)

going right down, we get : alpha |-> yoneda alpha |-> F (f) (phi alpha)      = F(f) (alpha_b(id_b))
going down right, we get : alpha |-> alpha o C(f,-) |-> phi (alpha o C(f,-)) = (alpha o C(f,-))_a (id_a)

for the diagram to commute, we need to prove
F(f) (alpha_b(id_b)) = (alpha o C(f,-))_a (id_a)
------------------------------------------------ rw [vertical composition]
F(f) (alpha_b(id_b)) = alpha_a (C(f,-)_a o id_a)
---------------------------------------------- rw [definition of C(f,-)_a]
F(f) (alpha_b(id_b)) = alpha_a (id_a o f)
----------------------------------------- simp
F(f) (alpha_b(id_b)) = alpha_a f

the above holds if the following diagram commutes

  C(b,b) --- C(b,f) ---> C(b,a)
    |                       |
  alpha_b                     alpha_a
    |                       |
    V                       V
  F(b)  ----- F(f) ----->  F(a)

going right down, we get : (alpha_a  C(b,f)) C(b,b)
going down right, we get : (F(f) alpha_b) C(b,b)

alpha is natural, so we have that
F(f) alpha_b = alpha_a C(b,f) (*2)

(alpha_a  C(b,f)) C(b,b) = (F(f) alpha_b) C(b,b)
----------------------------------------------- rw [*2]
(alpha_a  C(b,f)) C(b,b) = (alpha_a C(b,f)) C(b,b)
-------------------------------------------------- refl
[]

QED
```

so in total:
forall categories C
forall objects a in C
forall functors F from C to whatever

we have that 

```
Nat(C(a,-),F(-)) ≅ F a
```

--------------------------------------------------------------------------------

1. Show that the two functions phi and psi that form the Yoneda isomorphism in
   Haskell are inverses of each other.

```haskell
phi :: (forall x . (a -> x) -> F x) -> F a
phi alpha = alpha id

psi :: F a -> (forall x . (a -> x) -> F x)
psi fa h = fmap h fa

```

```idris
phi : Functor f => 
    (forall x . (a -> x) -> f x) -> f a
phi alpha = alpha id

psi : Functor f => 
    f a -> (forall x . (a -> x) -> f x)
psi fa h = map h fa

phiPsi : Functor f => (fa : f a) -> phi (psi fa) = fa

phiPsiMaybe : (fa : Maybe a) -> phi {f=Maybe} (psi fa) = fa
phiPsiMaybe Nothing = Refl
phiPsiMaybe (Just x) = Refl

psiPhi : Functor f => (alpha : forall x. (a -> x) -> f x) 
      -> (y : Type) -> (h : a -> y) -> psi (phi alpha) h = alpha h


testPhi : Int -> Maybe Int
testPhi x = phi (\f => Just (f x))

testPsi : Int -> Maybe String
testPsi x = psi (Just x) show
```

2. A discrete category is one that has objects but no morphisms other than
   identity morphisms. How does the Yoneda lemma work for functors from such a
   category?

3. A list of units [()] contains no other information but its length. So, as a
   data type, it can be considered an encoding of integers. An empty list
   encodes zero, a singleton [()] (a value, not a type) encodes one, and so on.
   Construct another representation of this data type using the Yoneda lemma
   for the list functor.
