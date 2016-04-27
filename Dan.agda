open import Preliminaries
open Vector using (Vec ; [] ; _::_)

module Dan where
  infix 80 sCtx

  data Tp : Set where
    P : Tp
    Q : Tp

  data Ctx : Set where
    · : Ctx
    sCtx : Tp → Ctx
    _,_ : Ctx → Ctx → Ctx

  data _≡_ : Ctx → Ctx → Set where
    emp : · ≡ ·
    leaf : ∀ {A} → sCtx A ≡ sCtx A
    cong : ∀{Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ≡ Δ₁ → Γ₂ ≡ Δ₂ → (Γ₁ , Γ₂) ≡ (Δ₁ , Δ₂)

  data _⊢s_ : Ctx → Ctx → Set where
    empty : · ⊢s ·
    var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
    comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
    equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ

  refl : ∀ {Γ} → Γ ≡ Γ
  refl {·} = emp
  refl {sCtx x} = leaf
  refl {Γ₁ , Γ₂} = cong refl refl

  sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
  sym emp = emp
  sym leaf = leaf
  sym (cong pf pf₁) = cong (sym pf) (sym pf₁)

  trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
  trans emp emp = emp
  trans leaf leaf = leaf
  trans (cong pf1 pf2) (cong pf3 pf4) = cong (trans pf1 pf3) (trans pf2 pf4)

  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂'
  dan .· .· Γ₁' Γ₂' empty ()
  dan ._ ._ Γ₁' Γ₂' var ()
  dan ._ ._ Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (cong eq1 eq2) = Γ₁ , Γ₂ , refl , equiv refl sub1 eq1 , equiv refl sub2 eq2
  dan Γ ._ Γ₁' Γ₂' (equiv x1 sub x2) (cong eq1 eq2) with dan _ _ _ _ sub x2
  ... | (Γ1 , Γ2 , split , sub1 , sub2) = Γ1 , Γ2 , trans split (sym x1) , equiv refl sub1 eq1 , equiv refl sub2 eq2
