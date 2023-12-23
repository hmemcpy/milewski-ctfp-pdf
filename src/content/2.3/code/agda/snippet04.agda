hom : (a → b) → Set
hom h = ∀{x y} → h (x *ᴬ y) ≡ h x *ᴮ h y
