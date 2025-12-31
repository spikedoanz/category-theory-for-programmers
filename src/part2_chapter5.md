https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/

0. Extra credit (by me):
Prove the Yoneda lemma

```
have:
  C         : Category
  F         : Functor (arbitrary)
  a         : Object in C
  C(a,-)    : Hom-functor / Presheaf
              this is both for objects C(a,x) and 
              morphisms C(a,-)(f) (this means action of hom-functor on morphism f)
  Nat       : Natural transformation
              otherwise read as alpha_x : C(a,x) -> F(x) forall x
prove:
  Nat(C(a,-),F(-)) ≅ F a ("the" yoneda lemma)
  + the above is naturally isomorphic in F
  + the above is naturally isomorphic in a

proof sketch:
    define p
        |
        V
    naturality square at a --> equation (*)
        |                           │
        |                           V
        |                     full square -> (*1)
        |                           |
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
  alpha_a                 alpha_x
    V                         V
  F(a) ----- F(g) ------>   F(x) 

specialize C(a,a) to id_a

  id_a   --- C(a,-)(g) ---> g
    |                       |
  alpha_a               alpha_x
    V                       V
    p ----- F(g) ------> F(g)(p) = alpha_x g

therefore, when we fix p:
  forall g: a -> x, forall x
  alpha_x g = F(g)(p) (*)

we draw the full naturality square 

  C(a,x) --- C(a,-)(f) ---> C(a,y)
    |                       |
  alpha_x               alpha_y
    V                       V
  F(x) ----- F(f) ------> F(y) 

rw C(a,x) for arbitrary g : a -> x
rw C(a,y) for application of C(a,-)(f) to C(a,x)

    g ------ C(a,-)(f) ---> f . g
    |                         |
  alpha_x                 alpha_y
    V                         V
 alpha_x g --- F(f) ------>  ???

going right, then down, we obtain

alpha_y (f . g)
------------- rw [*] where f g : a -> y
F(f . g)(p)
--------- rw [functor laws for F]
(F(f) . F(g)) (p)


going down, then right, we obtain

F(f) . (alpha_x g)
-------------- rw [*] where g : a -> x
(F(f) . F(g)) (p)

therefore, the full naturality square commutes when we define alpha^p_x(g) := F(g)(p) (*1)

this means alpha^p is a natural transformation, so psi is well-defined:
  psi : F(a) -> Nat(C(a,-), F)
  psi(p) := alpha^p         where       alpha^p_x (g) := F(g)(p)

we know from (*1) that alpha^p commutes, so psi(p) is a natural transformation
let phi(alpha) := alpha_a (id_a)

now we show that 

phi(psi(p)) = p 
---------------- rw [definition of psi]
phi(alpha^p) = p
----------------- rw [definition of phi]
alpha^p_a (id_a) = p
--------------------- rw [definition of alpha^p]
F(id_a)(p) = p
-------------- rw [functor preserves identity]
id_{F(a)}(p) = p
---------------- rw [apply id]
p = p
----- refl
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
  alpha_a               alpha_x
    |                       |
    V                       V
  F(a) ----- F(g) ------> F(x) 

rw [uniqueness of id_a in C(a,a)]

   id_a  ---------- C(a,-)(g) -----> g
    |                                |
  alpha_a                        alpha_x
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

--------------------------------------------------------------------------------

to prove that the yoneda lemma describes a natural isomorphism in F, we need to show that
forall natural transformations beta from F to an arbitrary functor G, beta is natural.


  Nat(C(a,-), F) --- phi -------> F(a)
      |                             |
  beta_-                        beta_a
      V                             V
  Nat(C(a,-),G) --- phi --- > G(a)


going right down, we get : alpha |-> phi (alpha) = alpha_a (id_a) 
    |-> beta_a (alpha_a (id_a))
going down right, we get : alpha |-> beta . alpha                 
    |-> phi (beta . alpha) = (beta . alpha)_a (id_a) 
    =   beta_a (alpha_a (id_a))

by refl, these are equal, which shows that beta satisfies the naturality conditions.

we also need to prove that the yoneda lemma describes a natural isomorphism in a, which means showing that
forall b
forall f: b -> a
let alpha' in Nat(C(b,-),F)

note: C(-,a)(f) : C(a,a) -> C(b, a)    given by    (g : a -> a) |-> (g . f : b -> a)

the following square commutes:
  
  alpha'        --- phi --->  F(b)
    |                             |
  - * C(-,a)(f)                     F(f)
    V                             V
  Nat(C(a,-),F) --- phi ---> F(a)

going right down, we get : alpha' |-> phi alpha' |-> F (f) (phi alpha')      = F(f) (alpha'_b(id_b))
going down right, we get : alpha' |-> alpha' * C(-,a)(f) |-> phi (alpha' * C(-,a)(f)) = (alpha' * C(-,a)(f))_a (id_a)

for the diagram to commute, we need to prove
F(f) (alpha'_b(id_b)) = (alpha' * C(-,a)(f))_a (id_a)
------------------------------------------------ rw [vertical composition]
F(f) (alpha'_b(id_b)) = alpha'_a (C(-,a)(f)_a id_a)
---------------------------------------------- rw [definition of C(-,a)(f)_a]
F(f) (alpha'_b(id_b)) = alpha'_a (id_a . f)
----------------------------------------- simp
F(f) (alpha'_b(id_b)) = alpha'_a f

the above holds if the following diagram commutes

  C(b,b) --- C(b,-)(f) ---> C(b,a)
    |                          |
  alpha'_b                 alpha'_a
    V                          V
  F(b)  ----- F(f) ------->  F(a)

going right down, we get : id_b |-> f . id_b = f    |-> alpha'_a (f)
going down right, we get : id_b |-> alpha'_b (id_b) |-> F(f) (alpha'_b (id_b))

alpha' is natural, so we have that
F(f) . alpha'_b = alpha'_a . C(b,-)(f)    (*2)

alpha'_a (f) = F(f) (alpha'_b (id_b))
------------------------------------- rw [naturality of alpha' at f : b -> a, applied to id_b]
alpha'_a (f) = alpha'_a (f)
--------------------------- refl
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

this proof was zero shot by opus after i plugged in my explicit proof of the
yoneda lemma:
```idris
record LawfulFunctor (f : Type -> Type) where
  constructor MkLawfulFunctor
  fmap : forall a, b. (a -> b) -> f a -> f b
  identity : forall a. (fa : f a) -> fmap Prelude.id fa = fa
  composition : forall a, b, c. (g : a -> b) -> (h : b -> c) -> (fa : f a)
             -> fmap (h . g) fa = fmap h (fmap g fa)

Reader : Type -> Type -> Type
Reader a x = a -> x

ReaderFunctor : (a : Type) -> LawfulFunctor (Reader a)
ReaderFunctor a = MkLawfulFunctor
  (\h, g => h . g)
  (\g => Refl)
  (\g, h, k => Refl)

record NatTrans (f, g : Type -> Type) (ff : LawfulFunctor f) (fg : LawfulFunctor g) where
  constructor MkNat
  component : forall x. f x -> g x
  naturality : forall x, y. (h : x -> y) -> (fx : f x)
            -> fmap fg h (component fx) = component (fmap ff h fx)

phi : (ff : LawfulFunctor f) 
   -> NatTrans (Reader a) f (ReaderFunctor a) ff 
   -> f a
phi ff nt = component nt Prelude.id

psi : (ff : LawfulFunctor f)
   -> (fa : f a)
   -> NatTrans (Reader a) f (ReaderFunctor a) ff
psi ff fa = MkNat
  (\h => fmap ff h fa)
  (\h, g => sym (composition ff g h fa))

phiPsi : (ff : LawfulFunctor f)
      -> (fa : f a)
      -> phi ff (psi ff fa) = fa
phiPsi ff fa = identity ff fa

psiPhi : (ff : LawfulFunctor f)
      -> (nt : NatTrans (Reader a) f (ReaderFunctor a) ff)
      -> (h : a -> x)
      -> component (psi ff (phi ff nt)) h = component nt h
psiPhi ff nt h = rewrite sym (naturality nt h Prelude.id) in Refl
```

--------------------------------------------------------------------------------

2. A discrete category is one that has objects but no morphisms other than
   identity morphisms. How does the Yoneda lemma work for functors from such a
   category?

C(a,-) will just be
  cases - of
  a => {id_a}
  _ => {}

the yoneda lemma says that maps out of C(a,-) will be entirely determined by
what F does to a, which in this case, does nothing besides pick an element out
of F a.

--------------------------------------------------------------------------------

3. A list of units [()] contains no other information but its length. So, as a
   data type, it can be considered an encoding of integers. An empty list
   encodes zero, a singleton [()] (a value, not a type) encodes one, and so on.
   Construct another representation of this data type using the Yoneda lemma
   for the list functor.

in other words, this question is asking, 
specialize a = ()
specialize F = List
show: what does the lhs of this expression look like?

Nat( C( () , -), List) ≅ List ()

so basically, what is:

Nat( C( () , -), List)?

well, in idris, this is
```idris
lhs : forall x. (() -> x) -> List x
lhs lam = [] -- or literally whatever you want
```


