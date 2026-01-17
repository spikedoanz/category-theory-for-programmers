https://bartoszmilewski.com/2016/04/18/adjunctions/

1. Derive the naturality square for ψ, the transformation between the two
   (contravariant) functors:

a -> C(L a, b)
a -> D(a, R b)

proved in full in 3

--------------------------------------------------------------------------------

2. Derive the counit ε starting from the hom-sets isomorphism in the second
   definition of the adjunction.

proved in full in 3

--------------------------------------------------------------------------------

3. Complete the proof of equivalence of the two definitions of the adjunction.

================================================================================
have:
  C, D : Category
  L : Functor D -> C
  R : Functor C -> D

definition 1 (unit/counit):
  η : Nat(I_D, R ∘ L)         -- for each d: η_d : d -> R(L(d))
  ε : Nat(L ∘ R, I_C)         -- for each c: ε_c : L(R(c)) -> c
  triangle 1: ε_{L d} ∘ L(η_d) = id_{L d}
  triangle 2: R(ε_c) ∘ η_{R c} = id_{R c}

definition 2 (hom-set):
  C(L d, c) ≅ D(d, R c)   -- natural in d and c

prove
  definition 1 <-> definition 2
================================================================================
proof:

## def 1 -> def 2:

define φ   : C(L d, c) -> D(d, R c)
  for f : L d -> c
  φ(f) := R(f) ∘ η_d

  d --- η_d -->  R L d --- R(f) --> R c

define φ⁻¹ : D(d, R c) -> C (L d, c)
  for g : d -> R c
  φ⁻¹(g) := ε_c ∘ L(g)
  
  L d --- L(g) --> L R c --- ε_c --> c


### we need to show that φ⁻¹(φ(f)) = f

φ⁻¹(φ(f))
---------- rw [def φ]
φ⁻¹(R(f) ∘ η_d)
--------------- rw [def φ⁻¹]
ε_c ∘ L(R(f) ∘ η_d))
-------------------- functoriality of L
ε_c ∘ L(R(f)) ∘ L(η_d)
---------------------- naturality of ε at f
f ∘ ε_{L d} ∘ L(η_d)
-------------------- rw [triangle 1]
f ∘ id_{L d}
------------ simp
f
-
[]


### we need to show that φ(φ⁻¹(g)) = g

φ(φ⁻¹(g))
--------- rw [def φ⁻¹]
φ(ε_c ∘ L(g))
------------- rw [def φ]
R(ε_c ∘ L(g)) ∘ η_d
------------------- functoriality of R
R(ε_c) ∘ R(L(g)) ∘ η_d
---------------------- naturality of η at g
R(ε_c) ∘ η_{R c} ∘ g
-------------------- rw [triangle 2]
id_{R c} ∘ g
------------ simp
g
-
[]


### we need to show that φ is natural in c
  for h : c -> c'
  need R(h) ∘ φ(f) = φ(h ∘ f)

R(h) ∘ φ(f) 
----------- rw [def φ]
R(h) ∘ R(f) ∘ η_d 
------------------ functoriality of R
R(h∘ f) ∘ η_d 
-------------- rw [<- def φ]
φ(h ∘ f)
--------
[]


### we need to show that φ is natural in d
  for k : d' -> d
  need φ(f) ∘ k = φ(f ∘ L(k))

φ(f) ∘ k
-------- rw [def φ]
R(f) ∘ η_d ∘ k
-------------- naturality of η_d at k
R(f) ∘  R(L(k)) ∘ η_{d'}
------------------------ rw fuctoriality of R
R(f ∘ L(k)) ∘ η_{d'}
-------------------- rw [<- def φ]
φ(f ∘ L(k))
-----------
[]

QED

================================================================================

# def 2 -> def 1

have:
  C, D : Category
  L : Functor D -> C
  R : Functor C -> D
  φ : C(L d, c) -> D(d, R c)      -- left to right
  ψ : D(d, R c) -> C(L d, c)      -- right to left
  ψ ∘ φ = id
  φ ∘ ψ = id
  φ natural in d and c
  ψ natural in d and c

prove:
  η : Nat(I_D, R ∘ L)
  ε : Nat(L ∘ R, I_C)
  triangle 1: ε_{L d} ∘ L(η_d) = id_{L d}
  triangle 2: R(ε_c) ∘ η_{R c} = id_{R c}

================================================================================

define η_d : d -> R(L d)
  set c = L d in φ : C(L d, c) -> D(d, R c)
  φ : C(L d, L d) -> D(d, R L d)
  η_d := φ(id_{L d})

define ε_c : L(R c) -> c
  set d = R c in ψ : D(d, R c) -> C(L d, c)
  ψ : D(R c, R c) -> C(L R c, c)
  ε_c := ψ(id_{R c})

--------------------------------------------------------------------------------
### show η natural:
  for k : d' -> d
  need: R(L(k)) ∘ η_{d'} = η_d ∘ k

  naturality of φ in c says:
    for h : c -> c'
    R(h) ∘ φ(f) = φ(h ∘ f)

  set c = L d', c' = L d, h = L(k), f = id_{L d'}:
    R(L(k)) ∘ φ(id_{L d'}) = φ(L(k) ∘ id_{L d'})
    ------------------------ rw [def η]
    R(L(k)) ∘ η_{d'} = φ(L(k))                     (*)

  naturality of φ in d says:
    for k : d' -> d
    φ(f) ∘ k = φ(f ∘ L(k))

  set f = id_{L d}:
    φ(id_{L d}) ∘ k = φ(id_{L d} ∘ L(k))
    ------------------- rw [def η]
    η_d ∘ k = φ(L(k))                              (**)

  combining (*) and (**):
    R(L(k)) ∘ η_{d'} = φ(L(k)) = η_d ∘ k
  []

--------------------------------------------------------------------------------
### show ε natural:
  for h : c -> c'
  need: ε_{c'} ∘ L(R(h)) = h ∘ ε_c

  naturality of ψ in d says:
    for k : d' -> d
    ψ(g) ∘ L(k) = ψ(g ∘ k)

  set d' = R c, d = R c', k = R(h), g = id_{R c'}:
    ψ(id_{R c'}) ∘ L(R(h)) = ψ(id_{R c'} ∘ R(h))
    ------------------------ rw [def ε]
    ε_{c'} ∘ L(R(h)) = ψ(R(h))                     (*)

  naturality of ψ in c says:
    for h : c -> c'
    h ∘ ψ(g) = ψ(R(h) ∘ g)

  set g = id_{R c}:
    h ∘ ψ(id_{R c}) = ψ(R(h) ∘ id_{R c})
    ----------------- rw [def ε]
    h ∘ ε_c = ψ(R(h))                              (**)

  combining (*) and (**):
    ε_{c'} ∘ L(R(h)) = ψ(R(h)) = h ∘ ε_c
  []

--------------------------------------------------------------------------------
### show triangle 1: ε_{L d} ∘ L(η_d) = id_{L d}

  naturality of ψ in d says:
    for k : d' -> d
    ψ(g) ∘ L(k) = ψ(g ∘ k)

  set d' = d, d = R L d, k = η_d : d -> R L d, c = L d, g = id_{R L d}:
    ψ(id_{R L d}) ∘ L(η_d) = ψ(id_{R L d} ∘ η_d)
    ------------------------ rw [def ε at c = L d]
    ε_{L d} ∘ L(η_d) = ψ(η_d)
    ------------------------- rw [def η]
    ε_{L d} ∘ L(η_d) = ψ(φ(id_{L d}))
    --------------------------------- rw [ψ ∘ φ = id]
    ε_{L d} ∘ L(η_d) = id_{L d}
  []

--------------------------------------------------------------------------------
### show triangle 2: R(ε_c) ∘ η_{R c} = id_{R c}

  naturality of φ in c says:
    for h : c -> c'
    R(h) ∘ φ(f) = φ(h ∘ f)

  set c = L R c, c' = c, h = ε_c : L R c -> c, d = R c, f = id_{L R c}:
    R(ε_c) ∘ φ(id_{L R c}) = φ(ε_c ∘ id_{L R c})
    ------------------------ rw [def η at d = R c]
    R(ε_c) ∘ η_{R c} = φ(ε_c)
    ------------------------- rw [def ε]
    R(ε_c) ∘ η_{R c} = φ(ψ(id_{R c}))
    --------------------------------- rw [φ ∘ ψ = id]
    R(ε_c) ∘ η_{R c} = id_{R c}
  []

QED

--------------------------------------------------------------------------------

4. Show that the coproduct can be defined by an adjunction. Start with the
   definition of the factorizer for a coproduct.

a coproduct a + b for given objects a and b is defined by two functions
i1 : a -> a + b
i2 : b -> a + b

the factorizer for a coproduct can be defined via two functions
f : a -> c
g : b -> c

which produces a unique [f,g] : (a + b) -> c s.t
i1 [f,g] = f
i2 [f,g] = g

we can characterize the coproduct via an adjunction:

C(a+b,c) ≅ C(a,c) x C(b,c)

the coproduct functor - + - : C x C -> C is left adjoint to the diagonal
functor Δ: C -> C x C

we can find the unit and counits of this adjunction:

unit    : Id_{CxC} -> Δ ∘ (+)
  at (a,b), we need (a,b) -> (a+b, a+b), which is (i1, i2)
η = (i1, i2)

counit  : (+) ∘ Δ -> Id_{C} 
  at c, we need c + c -> c, which is [id_c, id_c]
ε = [id_c, id_c]






triangle identities:
  triangle 1:
  ε_{a+b} ∘ (+)(η_{a+b}) = id_{a+b}
----------------------------------- simp
  ε_{a+b} ∘ (+)(η_{a+b}) = (a+b, a+b)
------------------------------------- def η
  ε_{a+b} ∘ (+)( (i1,i2)(a+b) ) = (a+b, a+b)
-------------------------------------------- simp
  ε_{a+b} ∘ (+)( a+b, a+b ) = (a+b, a+b)
---------------------------------------- def (+)
  ε_{a+b} ∘ ((a+b) + (a+b)) = (a+b, a+b)
-------------------------------------- def ε
  [id_{a+b}, id_{a+b}] ((a+b) + (a+b)) = (a+b, a+b)
--------------------------------------------------- simp
  (a+b, a+b) = (a+b, a+b)
------------------------- rfl
  []


  triangle 2:
  Δ(ε_c) ∘ η_{Δ(c)} = id_{Δ(c)}
------------------------------- def Δ
  Δ(ε_c) ∘ η_{(c,c)} = id_{(c,c)}
--------------------------------- def η
  Δ(ε_c) ∘ (i1,i2)(c,c) = id_{(c,c)}
------------------------------------ simp
  Δ(ε_c) ∘ ((c,c), (c,c)) = id_{(c,c)}
-------------------------------------- def ε
  Δ([id_c, id_c]) ∘ ((c,c), (c,c)) = id_{(c,c)}
----------------------------------------------- def Δ
  ([id_c, id_c], [id_c, id_c]) ∘ ((c,c), (c,c)) = id_{(c,c)}
------------------------------------------------------------ simp
  ([id_c, id_c] ∘ (c,c), [id_c, id_c] ∘ (c,c)) = id_{(c,c)}
----------------------------------------------------------- simp
  (c , c) = id_{(c,c)}
  
--------------------------------------------------------------------------------

5. Show that the coproduct is the left adjoint of the diagonal functor.

proved in (4)

--------------------------------------------------------------------------------

6. Define the adjunction between a product and a function object in Haskell.


(a,b) -> c ≅ a -> (b -> c)

```idris
unit    : a -> b -> (a,b)
unit a b = (a,b)

counit  : (b -> c, b) -> c
counit (f, b) = f b

triangle1 : (p: (a,b)) -> counit (unit (fst p), snd p) = p
triangle1 (a,b) = Refl

triangle2 : (f : b -> c) -> (x: b) -> counit (f, x) = f x
triangle2 f x = Refl
```
