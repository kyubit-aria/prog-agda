module magic-cw where
import Relation.Binary.PropositionalEquality as Eq

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


record IsMagical {A : Set} (_∙_ : A → A → A) : Set where
  field
    left         : ∀ x y → (x ∙ y) ∙ y  ≡  x
    right        : ∀ x y → y ∙ (y ∙ x)  ≡  x


record IsCommuntative {A : Set} (_∙_ : A → A → A) : Set where
  field
    comm         : ∀ x y → x ∙ y  ≡ y ∙ x



open IsMagical
open IsCommuntative

magic-is-commutative : {A : Set}
  (_∙_ : A → A → A)
  → IsMagical _∙_
  → IsCommuntative _∙_
magic-is-commutative {A} f m@record { left = l ; right = r } =
  record { comm = λ x y →
           f x y
             ≡⟨ magic-l-r-id f x (f x y) (f y x) m (magic-l-r-eq f x y m) ⟩             
           f y x ∎
         }
  where
    magic-l-r-eq : (_∙_ : A → A → A)
                      → (x y : A)
                      → IsMagical _∙_
                      → (x ∙ (x ∙ y) ≡ (y ∙ x) ∙ x)
    magic-l-r-eq _∙_ x y m'@record { left = l' ; right = r' } =
                           (x ∙ (x ∙ y))
                               ≡⟨ r' y x ⟩
                           y
                               ≡⟨ sym (l' y x) ⟩
                           ((y ∙ x) ∙ x) ∎ 
    
    magic-l-r-id : (_∙_ : A → A → A)
                      → (x y z : A)
                      → (IsMagical _∙_)
                      → (x ∙ y ≡ z ∙ x)
                      → (y ≡ z)
    magic-l-r-id _∙_ x y z record { left = l' ; right = r' } xy≡zx =
                 y
                   ≡⟨ sym (r' y (z ∙ x)) ⟩
                 (z ∙ x) ∙ ((z ∙ x) ∙ y)
                   ≡⟨ cong (λ e → (z ∙ x) ∙ (e ∙ y)) (sym xy≡zx) ⟩
                 (z ∙ x) ∙ ((x ∙ y) ∙ y)
                   ≡⟨ cong (λ e → (z ∙ x) ∙ e) (l' x y) ⟩
                 (z ∙ x) ∙ x
                   ≡⟨ l' z x ⟩
                 z ∎
