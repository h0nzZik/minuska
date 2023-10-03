
## Specification language

Here is a bunch of examples illustrating
what language specifications want to support.
r,s,t,... - symbols
x,y,z,... - variables
1,2,3,... - builtins
+,*,...   - binary operators

G1. Rewrite builtins to expressions (using local rewrite)
```
    1 => (2 + 3)
```

G2. Rewrite possibly constrained variables to expressions
```
    (x where x >= 1) => (x + 1)
```

G3. Both (1) and (2) in a term context, locally
```
    t (1 => (2 + 3)) ((x where x >= 1) => (x + 1))
```


G4. Variable sharing across local rewrites
```
    t (x => y) (y => x)
```

G5. Constraints on top of a rewrite rule
```
    (t (x => y) z) where x >= z
```

G6. Constraints inside rewrite rule
```
    t ((x => y) where x >= 0) (z where z >= 0)
```


Here are examples illustrating what we do NOT want to support.

B1. Rewrites of symbols
```
    (t => s) x
```

B2. Rewrites of partial applications
```
    (t x => s x) y
```

B3. Rewrite terms to builtins
```
    (t x 3) => 4
```

B4. Rewrite expressions
```
    (x + 3) => x
```