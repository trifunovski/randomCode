open import Preliminaries
open Vector using (Vec ; [] ; _::_)

module IntuitionisticLogic where
  infix 80 sCtx
  infix 81 _⊗_
  infix 82 _⊸_
  infix 80 _≡_

  data Tp : Set where
    P : Tp
    Q : Tp
    _⊗_ : Tp → Tp → Tp
    _⊸_ : Tp → Tp → Tp
    1o : Tp
    ⊤o : Tp
    0o : Tp

  data Ctx : Set where
    · : Ctx
    sCtx : Tp → Ctx
    _,_ : Ctx → Ctx → Ctx

  data _∈_ (A : Tp) : Ctx → Set where
    S : A ∈ (sCtx A)
    ML : ∀ {Γ₁ Γ₂ : Ctx} → A ∈ Γ₁ → A ∈ (Γ₁ , Γ₂)
    MR : ∀ {Γ₁ Γ₂ : Ctx} → A ∈ Γ₂ → A ∈ (Γ₁ , Γ₂)

  data _⊢_ : Ctx → Tp → Set where
    ax : ∀ {Γ A} → A ∈ Γ → Γ ⊢ A
    cut : ∀ {Γ Δ A C} → Γ ⊢ A → (Δ , sCtx A) ⊢ C → (Γ , Δ) ⊢ C
    ⊗R : ∀ {Γ Δ A B} → Γ ⊢ A → Δ ⊢ B → (Γ , Δ) ⊢ A ⊗ B
    ⊗L : ∀ {Γ A B C} → (Γ , (sCtx A , sCtx B)) ⊢ C → (Γ , sCtx (A ⊗ B)) ⊢ C
    1R : · ⊢ 1o
    1L : ∀ {Γ C} → Γ ⊢ C → (Γ , sCtx 1o) ⊢ C
    ⊸R : ∀ {Γ A B} → (Γ , sCtx A) ⊢ B → Γ ⊢ A ⊸ B
    ⊸L : ∀ {Γ Δ A B C} → Γ ⊢ A → Γ ⊢ B → (Γ , (Δ , sCtx (A ⊸ B))) ⊢ C

  data _≡_ : Ctx → Ctx → Set where
    refl : ∀ {Γ} → Γ ≡ Γ
    sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
    trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
    cong : ∀{Γ Γ' Δ Δ'} → Γ ≡ Δ → Γ' ≡ Δ' → (Γ , Γ') ≡ (Δ , Δ')
    comm : ∀{Γ₁ Γ₂} → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
    assoc : ∀{Γ₁ Γ₂ Γ₃} → ((Γ₁ , Γ₂) , Γ₃) ≡ (Γ₁ , (Γ₂ , Γ₃))
    unit : ∀{Γ} → (· , Γ) ≡ Γ

  data _⊢s_ : Ctx → Ctx → Set where
    empty : · ⊢s ·
    var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
    comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
    equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ


  mutual
    lemma : ∀{Γ₁' Γ₂'} → · ≡ (Γ₁' , Γ₂') → · ≡ Γ₁' × · ≡ Γ₂'
    lemma (sym (sym pf)) = lemma pf
    lemma (sym unit) = refl , refl
    lemma (sym (trans pf pf₁)) = {!!}
    lemma (trans pf pf₁) = {!!}


    lemmaHelper : ∀ {Γ Γ' Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ · → Γ ≡ ·
    lemmaHelper eq1 empty refl = eq1
    lemmaHelper eq1 (equiv x sub x₁) refl = trans eq1 (lemmaHelper x sub x₁)
    lemmaHelper eq1 (comma sub sub₁) unit with lemmaEmpty sub | lemmaEmpty sub₁
    ... | pf1 | pf2 = trans (trans eq1 (cong pf1 pf2)) unit
    lemmaHelper eq1 (equiv x sub x₁) unit = lemmaHelper (trans eq1 x) sub (trans x₁ unit)
    lemmaHelper eq empty (sym pf) = eq
    lemmaHelper eq var (sym pf) = trans eq (sym pf)
    lemmaHelper eq (comma sub1 sub2) (sym pf) with lemma pf
    lemmaHelper eq (comma sub1 sub2) (sym pf) | fst , snd with lemmaHelper refl sub1 (sym fst) | lemmaHelper refl sub2 (sym snd)
    ... | lem1 | lem2 = trans (trans eq (cong lem1 lem2)) unit
    lemmaHelper eq (equiv x1 sub x2) (sym pf) = trans eq (lemmaHelper x1 sub (trans x2 (sym pf)))
    lemmaHelper eq empty (trans pf1 pf2) = eq
    lemmaHelper eq var (trans pf1 pf2) = trans (trans eq pf1) pf2
    lemmaHelper eq (comma sub1 sub2) (trans pf1 pf2) with lemma (sym (trans pf1 pf2))
    lemmaHelper eq (comma sub1 sub2) (trans pf1 pf2) | fst , snd with lemmaHelper refl sub1 (sym fst) | lemmaHelper refl sub2 (sym snd)
    ... | lem1 | lem2 = trans (trans eq (cong lem1 lem2)) unit
    lemmaHelper eq (equiv x1 sub x2) (trans pf1 pf2) = trans eq (lemmaHelper x1 sub (trans x2 (trans pf1 pf2)))

    lemmaEmpty : ∀ {Γ} → Γ ⊢s · → Γ ≡ ·
    lemmaEmpty empty = refl
    lemmaEmpty (equiv {Γ}{Γ'}{Δ' = Δ'} x sub x₁) = lemmaHelper x sub x₁

    lemmaEmpty2 : ∀ {Γ} → · ≡ Γ → · ⊢s Γ
    lemmaEmpty2 refl = empty
    lemmaEmpty2 (sym refl) = empty
    lemmaEmpty2 (sym (sym pf)) = lemmaEmpty2 pf
    lemmaEmpty2 (sym unit) = equiv (sym unit) (comma empty empty) refl
    lemmaEmpty2 (sym (trans pf pf₁)) = {!!}
    lemmaEmpty2 (trans pf pf₁) = {!!}


  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂'
  dan .· .· .· .· empty (sym unit) = · , · , unit , empty , empty
  dan ._ ._ .· ._ (var {A = A}) (sym unit) = · , sCtx A , unit , empty , var
  dan ._ .(Γ₁' , Γ₂') Γ₁' Γ₂' (comma {Γ₁}{Γ₂} sub sub₁) refl = Γ₁ , Γ₂ , refl , sub , sub₁
  dan ._ ._ Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub sub₁) (cong eq eq₁) = Γ₁ , Γ₂ , refl , equiv refl sub eq , equiv refl sub₁ eq₁
  dan ._ .(Γ₂' , Γ₁') Γ₁' Γ₂' (comma {Γ₁}{Γ₂} sub sub₁) comm = Γ₂ , Γ₁ , comm , sub₁ , sub
  dan ._ ._ Γ₁' ._ (comma {Γ₁ = Γ₁}{Γ₂ = Γ₂}{Δ₂ = Δ₂} sub sub₁) (assoc {Γ₂ = exG}) with dan Γ₁ (Γ₁' , exG) Γ₁' exG sub refl
  ... | Γ1 , Γ2 , split , sub1 , sub2 = Γ1 , (Γ2 , Γ₂) , trans (sym assoc) (cong split refl) , sub1 , comma sub2 sub₁
  dan ._ ._ .· ._ (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub sub₁) ((sym unit) ) = · , (Γ₁ , Γ₂) , unit , empty , comma sub sub₁
  dan ._ .(· , (Γ₁' , Γ₂')) Γ₁' Γ₂' (comma {Γ₂ = Γ₂} sub sub₁) unit with dan Γ₂ (Γ₁' , Γ₂') Γ₁' Γ₂' sub₁ refl | lemmaEmpty sub
  ... | Γ1 , Γ2 , split , sub1 , sub2 | pf = Γ1 , Γ2 , trans (sym unit) (cong (sym pf) split) , sub1 , sub2
  dan Γ Γ' Γ₁' Γ₂' (equiv {Γ' = Γ''} {Δ' = Δ''} ΓeqΓ' sub Δ'eqΓ') eq with dan Γ'' Δ'' Γ₁' Γ₂' sub (trans Δ'eqΓ' eq)
  dan Γ Γ' Γ₁' Γ₂' (equiv ΓeqΓ' sub Δ'eqΓ') eq | Γs₁ , Γs₂ , seq , ssub1 , ssub2 = Γs₁ , (Γs₂ , ((trans seq (sym ΓeqΓ')) , (ssub1 , ssub2)))
  dan ._ .(Γ₁' , Γ₂') Γ₁' Γ₂' (comma {Γ₁}{Γ₂} sub sub₁) (sym refl) = Γ₁ , Γ₂ , refl , sub , sub₁
  dan Γ Γ' Γ₁' Γ₂' sub (sym (sym rest)) = dan Γ Γ' Γ₁' Γ₂' sub rest
  dan ._ ._ Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub sub₁) (sym (cong rest1 rest2)) = Γ₁ , Γ₂ , refl , equiv refl sub (sym rest1) , equiv refl sub₁ (sym rest2)
  dan ._ .(Γ₂' , Γ₁') Γ₁' Γ₂' (comma {Γ₁}{Γ₂} sub sub₁) (sym comm) = Γ₂ , Γ₁ , comm , sub₁ , sub
  dan ._ ._ ._ Γ₂' (comma {Γ₁}{Γ₂}{Δ₁} sub sub₁) (sym (assoc {Γ₂ = exG})) with dan Γ₂ (exG , Γ₂') Γ₂' exG sub₁ comm
  ... | (Γ1 , Γ2 , split , sub1 , sub2) = (Γ₁ , Γ2) , Γ1 , trans assoc (cong (refl {Γ₁}) (trans comm split)) , comma sub sub2 , sub1
  dan Γ ._ Γ₁' Γ₂' sub (sym (trans rest rest₁)) = {!!} -- dan _ _ _ _ (equiv refl (comma sub sub₁) (sym rest₁)) (sym rest)
  dan Γ ._ Γ₁' Γ₂' sub (trans rest rest₁) = {!!}

{-
  dan .· .· Γ₁' Γ₂' empty eq = {!Γ₁'!} -- · , (· , (unit , ({!!} , {!!})))
  dan ._ ._ Γ₁' Γ₂' var eq = {!!}
  dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) eq = {!!}
  dan Γ Γ' Γ₁' Γ₂' (equiv x sub x₁) eq = {!!}
-}
{-

  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → (ρ : Sub) → Γ ⊢[ ρ ] Γ' → Γ' ≡ (Γ₁' , Γ₂')
                           → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] Σ[ ρ₁ ∈ Sub ] Σ[ ρ₂ ∈ Sub ] (Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢[ ρ₁ ] Γ₁' × Γ₂ ⊢[ ρ₂ ] Γ₂' × (ρ₁ , ρ₂) ≡s ρ
  dan · Γ' Γ₁' Γ₂' ε (tr x) (iso x₁ x₂) = · , (· , (ε , (ε , (refl-≡ lemma0 , ((tr (λ x₃ → x (relax (iso x₁ x₂) (Inl x₃)))) , ((tr (λ x₃ → x (relax (iso x₁ x₂) (Inr x₃)))) , (isos {!!} {!!})))))))
  dan · Γ' Γ₁' Γ₂' (x for x₁) subpf split = {!!}
  dan · Γ' Γ₁' Γ₂' (ρ , ρ₁) subpf split = {!!}
  dan (sCtx x) Γ' Γ₁' Γ₂' ρ subpf split = {!!}
  dan (Γ , Γ₁) Γ' Γ₁' Γ₂' ρ subpf split = {!!}

-}
