1. Construct the Kleisli category for partial functions (define composition and
   identity).

if we use Maybe as our surrogate for partial functions, we can define
composition and identity as such: 

```idris
partialId : a -> Maybe a
partialId x = Just x

-- composition: chain two partial functions
-- if the first fails, the whole thing fails
-- if the first succeeds, feed the result to the second
partialComposition : (b -> Maybe c) -> (a -> Maybe b) -> (a -> Maybe c)
partialComposition g f x = 
    case f x of
        Nothing => Nothing
        Just y  => g y
```


--------------------------------------------------------------------------------

2. Implement the embellished function `safe_reciprocal` that returns a valid
   reciprocal of its argument, if it’s different from zero.

```idris
safeReciprocal : Double -> Maybe Double
safeReciprocal x = if (x /= 0) then Just (1 / x) else Nothing
```

--------------------------------------------------------------------------------

3. Compose `safe_root` and `safe_reciprocal` to implement
   `safe_root_reciprocal` that calculates sqrt(1/x) whenever possible.

```idris
safeRoot : Double -> Maybe Double
safeRoot x = if (x >= 0) then Just (sqrt x) else Nothing
```

```idris
safeRootReciprocal = partialComposition safeRoot safeReciprocal
```
