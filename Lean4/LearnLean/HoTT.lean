inductive Path {a : Sort u} (x : a) : a -> Sort (u + 1) :=
| refl : Path x x

open Path

def inv : Path x y -> Path y x
| refl => refl

def cat : Path x y -> Path y z -> Path x z
| refl, refl => refl

def cat_refl_l : (p : Path x y) -> Path (cat refl p) p
| refl => refl

def cat_refl_r : (p : Path y x) -> Path (cat p refl) p
| refl => refl

def cat_inv_l : (p : Path x y) -> Path (cat (inv p) p) refl
| refl => refl

def cat_inv_r : (p : Path x y) -> Path (cat p (inv p)) refl
| refl => refl

def cat_assoc :
  (p : Path x y) -> (q : Path y z) -> (r : Path z w) ->
    Path (cat (cat p q) r) (cat p (cat q r))
| refl, refl, refl => refl

def ap (f : a -> b) : Path x y -> Path (f x) (f y)
| refl => refl

def ap_cat (f : a -> b) :
  (p : Path x y) -> (q : Path y z) ->
    Path (ap f (cat p q)) (cat (ap f p) (ap f q))
| refl, refl => refl

def ap_inv (f : a -> b) :
  (p : Path x y) -> Path (ap f (inv p)) (inv (ap f p))
| refl => refl

def transport (b : a -> Type) : (p : Path x y) -> b x -> b y
| refl => id

def transport_cat (b : a -> Type) (u : b x) :
  (p : Path x y) -> (q : Path y z) ->
    Path (transport b (cat p q) u) (transport b q (transport b p u))
| refl, refl => refl

def transport_ap (P : b -> Type) (f : a -> b) (u : P (f x)) :
  (p : Path x y) ->
    Path (transport P (ap f p) u) (transport (P ∘ f) p u)
| refl => refl

def transport_wut
  (P Q : a -> Type) (f : (x : a) -> P x -> Q x) (u : P x) :
    (p : Path x y) ->
      Path (transport Q p (f x u)) (f y (transport P p u))
| refl => refl

def apd {P : a -> Type} (f : (x : a) -> P x) :
  (p : Path x y) -> Path (transport P p (f x)) (f y)
| refl => refl

def homotopy {P : a -> Type} (f g : (x : a) -> P x) :=
  (x : a) -> Path (f x) (g x)

def homotopy_refl : homotopy f f :=
  fun x => refl

def homotopy_sym (h : homotopy f g) : homotopy g f :=
  fun x => inv (h x)

def homotopy_trans
  (hfg : homotopy f g) (hgh : homotopy g h) : homotopy f h :=
    fun x => cat (hfg x) (hgh x)