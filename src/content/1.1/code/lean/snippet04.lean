def f: A → B
def g: B → C
def h: C → D

h ∘ (g ∘ f) == (h ∘ g) ∘ f == h ∘ g ∘ f
