1. Consider some degenerate cases of a naturality condition and draw the
appropriate diagrams. For instance, what happens if either functor F or G map
both objects a and b (the ends of f :: a -> b) to the same object, e.g., F a =
F b or G a = G b? (Notice that you get a cone or a co-cone this way.) Then
consider cases where either F a = G a or F b = G b. Finally, what if you start
with a morphism that loops on itself — f :: a -> a?

case 1:
```
// https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJGIGEiXSxbNSwwLCJGIGIgPSBGIGEiXSxbNSw0LCJHIGIgPSBHIGEiXSxbMCw0LCJHIGEiXSxbMiwyLCJhIl0sWzMsMiwiYiJdLFsxLDIsImFscGhhIGIiLDJdLFswLDMsImFscGhhIGEiXSxbMywyLCJHIGYiXSxbMCwxLCJGIGYiLDJdLFs0LDUsImYiXSxbNSwxLCJGIl0sWzQsMCwiRiJdLFs0LDMsIkciXSxbNSwyLCJHIiwxXSxbMTAsOSwiIiwwLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFsxMCw4LCIiLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV1d
#align(center, diagram({
	node((-3, 4), [$F a$])
	node((2, 4), [$F b = F a$])
	node((2, 8), [$G b = G a$])
	node((-3, 8), [$G a$])
	node((-1, 6), [$a$])
	node((0, 6), [$b$])
	edge((2, 4), (2, 8), [$alpha b$], label-side: right, "->")
	edge((-3, 4), (-3, 8), [$alpha a$], label-side: left, "->")
	edge((-3, 8), (2, 8), [$G f$], label-side: left, "->")
	edge((-3, 4), (2, 4), [$F f$], label-side: right, "->")
	edge((-1, 6), (0, 6), [$f$], label-side: left, "->")
	edge((0, 6), (2, 4), [$F$], label-side: left, "->")
	edge((-1, 6), (-3, 4), [$F$], label-side: left, "->")
	edge((-1, 6), (-3, 8), [$G$], label-side: left, "->")
	edge((0, 6), (2, 8), [$G$], label-side: center, "->")
}))
```

naturality:

$$ \alpha b F f = G f \alpha a $$


case 2:
```
// https://q.uiver.app/#r=typst&q=WzAsNCxbMiwyLCJhIl0sWzMsMiwiYiJdLFswLDAsIkYgYSA9IEcgYSJdLFs1LDAsIkYgYiA9IEcgYiJdLFswLDEsImYiXSxbMCwyLCJGIiwyXSxbMCwyLCJHIiwwLHsib2Zmc2V0IjotM31dLFsxLDMsIkciLDJdLFsxLDMsIkYiLDAseyJvZmZzZXQiOi0zfV0sWzIsMywiRyBmIiwxXSxbMiwzLCJGIGYiLDEseyJvZmZzZXQiOi0zfV0sWzQsMTAsIiIsMCx7ImN1cnZlIjotMiwic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFs0LDksIiIsMix7ImN1cnZlIjoyLCJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJsZXZlbCI6M31dXQ==
#align(center, diagram({
	node((-1, 1), [$a$])
	node((0, 1), [$b$])
	node((-3, -1), [$F a = G a$])
	node((2, -1), [$F b = G b$])
	edge((-1, 1), (0, 1), [$f$], label-side: left, "->")
	edge((-1, 1), (-3, -1), [$F$], label-side: right, "->")
	edge((-1, 1), (-3, -1), [$G$], label-side: left, shift: 0.15, "->")
	edge((0, 1), (2, -1), [$G$], label-side: right, "->")
	edge((0, 1), (2, -1), [$F$], label-side: left, shift: 0.15, "->")
	edge((-3, -1), (2, -1), [$G f$], label-side: center, "->")
	edge((-3, -1), (2, -1), [$F f$], label-side: center, shift: 0.15, "->")
}))
```

alpha must be Id on F and G, so naturality is satisfied no matter what.


case 3:
```
// https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJhIl0sWzAsMywiRiBhIl0sWzMsMCwiRyBhIl0sWzAsMCwiZiJdLFswLDEsIkYiXSxbMCwyLCJHIl0sWzIsMiwiRyBmIl0sWzEsMSwiRiBmIiwwLHsiYW5nbGUiOjE4MH1dLFsxLDIsImFscGhhIGEiLDFdXQ==
#align(center, diagram({
	node((0, 0), [$a$])
	node((0, 3), [$F a$])
	node((3, 0), [$G a$])
	edge((0, 0), (0, 0), [$f$], label-side: left, "->", bend: 140deg, loop-angle: 90deg)
	edge((0, 0), (0, 3), [$F$], label-side: left, "->")
	edge((0, 0), (3, 0), [$G$], label-side: left, "->")
	edge((3, 0), (3, 0), [$G f$], label-side: left, "->", bend: 140deg, loop-angle: 90deg)
	edge((0, 3), (0, 3), [$F f$], label-side: left, "->", bend: 140deg, loop-angle: -90deg)
	edge((0, 3), (3, 0), [$alpha a$], label-side: center, "->")
}))
```

naturality

$$ alpha_a F f = G f alpha_a $$
