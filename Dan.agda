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

mutual
  data _empty : Ctx → Set where
    sinE : · empty
    mulE : ∀ {Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → (Γ₁ , Γ₂) empty

  data _decTo_and_ : Ctx → Ctx → Ctx → Set where
    SD : ∀{A} → sCtx A decTo sCtx A and ·
    MD1 : ∀ {A Γ₁' Γ₁ Γ₂} → Γ₁ decTo sCtx A and Γ₁' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁' , Γ₂)
    MD2 : ∀ {A Γ₂' Γ₁ Γ₂} → Γ₂ decTo sCtx A and Γ₂' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁ , Γ₂')

  data _≡_ : Ctx → Ctx → Set where
    emp : ∀{Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → Γ₁ ≡ Γ₂
    decom : ∀{Γ Γ' Δ Δ' A} → Γ decTo sCtx A and Γ' → Δ decTo sCtx A and Δ' → Γ' ≡ Δ' → Γ ≡ Δ

  data _⊢s_ : Ctx → Ctx → Set where
    emptySub : · ⊢s ·
    var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
    comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
    equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ

 -- {-# NO_TERMINATION_CHECK #-}
  eitherLemma : (Γ : Ctx) → Either (Γ empty) (Σ[ A ∈ Tp ] Σ[ Γ' ∈ Ctx ] Γ decTo sCtx A and Γ')
  eitherLemma · = Inl sinE
  eitherLemma (sCtx x) = Inr (x , (· , SD))
  eitherLemma (Γ₁ , Γ₂) with eitherLemma Γ₁
  eitherLemma (Γ₁ , Γ₂) | Inr (a , Γ' , pf) = Inr (a , ((Γ' , Γ₂) , MD1 pf))
  eitherLemma (Γ₁ , Γ₂) | Inl x with eitherLemma Γ₂
  eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inl x = Inl (mulE x₁ x)
  eitherLemma (Γ₁ , Γ₂) | Inl x₁ | Inr (a , Γ' , pf) = Inr (a , ((Γ₁ , Γ') , MD2 pf))

  emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
  emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
  emptyEquiv (decom () x₁ pf)

  refl : ∀{Γ} → Γ ≡ Γ
  refl = {!!}
  -- refl {Γ} with eitherLemma Γ
  -- refl {Γ} | Inl x = emp x x
  -- refl {Γ} | Inr (a , Γ' , pf) = decom pf pf (refl {Γ'})

  sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
  sym (emp x x₁) = emp x₁ x
  sym (decom x x₁ pf) = decom x₁ x (sym pf)

  lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
  lemma sinE (emp x x₁) = x₁
  lemma sinE (decom x x₁ pf) = abort (lemmaEmptyDecom sinE x)
  lemma (mulE empt empt₁) (emp x x₁) = x₁
  lemma (mulE {Γ₁}{Γ₂} empt empt₁) (decom x x₁ pf) = abort (lemmaEmptyDecom (mulE empt empt₁) x)

  lemmaEmptyDecom : ∀{Γ A Δ} → Γ empty → Γ decTo sCtx A and Δ → Void
  lemmaEmptyDecom sinE ()
  lemmaEmptyDecom (mulE empt empt₁) (MD1 decpf) = lemmaEmptyDecom empt decpf
  lemmaEmptyDecom (mulE empt empt₁) (MD2 decpf) = lemmaEmptyDecom empt₁ decpf

  anotherLemma : ∀ {Γ Δ A} → Γ ≡ (sCtx A , Δ) → Γ decTo sCtx A and Δ
  anotherLemma (emp x (mulE () x₂))
  anotherLemma (decom x (MD1 SD) pf) = {!!}
  anotherLemma (decom x (MD2 x₁) pf) = {!anotherLemma pf!}

  weirdLemma : ∀{Γ A Δ} → Γ decTo sCtx A and Δ → Γ ≡ (sCtx A , Δ)
  weirdLemma SD = decom SD (MD1 SD) (emp sinE (mulE sinE sinE))
  weirdLemma (MD1 pf) = {!!} --weirdLemma (MD1 (anotherLemma (weirdLemma pf)))
  weirdLemma (MD2 pf) = {!!}

  eqDec : ∀ {Γ A Δ₁ Δ₂} → Γ decTo sCtx A and Δ₁ → Δ₁ ≡ Δ₂ → Γ decTo sCtx A and Δ₂
  eqDec decpf eq = {!!}

  specificLemma : ∀ {Γ Γ' Δ Δ' A B} → Γ decTo sCtx A and Δ
                                    → Γ decTo sCtx B and Δ'
                                    → Γ' decTo sCtx B and Δ'
                                    → Γ' decTo sCtx A and Δ
  specificLemma SD SD SD = SD
  specificLemma (MD1 dec1) (MD1 dec2) (MD1 dec3) = MD1 (specificLemma dec1 dec2 dec3)
  specificLemma (MD1 dec1) (MD1 dec2) (MD2 dec3) = {!!}
  specificLemma (MD1 dec1) (MD2 dec2) (MD1 dec3) = {!!}
  specificLemma (MD1 dec1) (MD2 dec2) (MD2 dec3) = {!!}
  specificLemma (MD2 dec1) (MD1 dec2) (MD1 dec3) = {!!}
  specificLemma (MD2 dec1) (MD1 dec2) (MD2 dec3) = {!!}
  specificLemma (MD2 dec1) (MD2 dec2) (MD1 dec3) = {!!}
  specificLemma (MD2 dec1) (MD2 dec2) (MD2 dec3) = MD2 (specificLemma dec1 dec2 dec3)

  trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
  trans (emp x x₁) (emp x₂ x₃) = emp x x₃
  trans (emp x x₁) (decom x₂ x₃ pf2) = abort (lemmaEmptyDecom x₁ x₂)
  trans (decom x x₁ pf1) (emp x₂ x₃) = abort (lemmaEmptyDecom x₂ x₁)
  trans (decom x x₁ pf1) (decom x₂ x₃ pf2) = decom x (specificLemma x₁ x₂ (eqDec x₃ (sym pf2))) pf1 -- decom x (anotherLemma (trans (sym pf2) (weirdLemma x₁))) pf1


  comm : ∀{Γ₁ Γ₂} → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
  comm = {!!}
  -- comm {Γ₁}{Γ₂} with eitherLemma Γ₁
  -- comm | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD2 pf) comm
  -- comm {Γ₁}{Γ₂} | Inl x₁ with eitherLemma Γ₂
  -- ... | Inl x = emp (mulE x₁ x) (mulE x x₁)
  -- ... | Inr (A , Γ₂' , pf) = decom (MD2 pf) (MD1 pf) comm


  assoc : ∀{Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
  assoc = {!!}
  -- assoc {Γ₁}{Γ₂}{Γ₃} with eitherLemma Γ₁
  -- assoc | Inr (A , Γ₁' , pf) = decom (MD1 pf) (MD1 (MD1 pf)) assoc
  -- assoc {Γ₁}{Γ₂}{Γ₃} | Inl x with eitherLemma Γ₂
  -- assoc | Inl x₁ | Inr (A , Γ₂' , pf) = decom (MD2 (MD1 pf)) (MD1 (MD2 pf)) assoc
  -- assoc {Γ₁}{Γ₂}{Γ₃} | Inl x₁ | Inl x with eitherLemma Γ₃
  -- assoc | Inl x₂ | Inl x₁ | Inr (A , Γ₃' , pf) = decom (MD2 (MD2 pf)) (MD2 pf) assoc
  -- assoc | Inl x₂ | Inl x₁ | Inl x = emp (mulE x₂ (mulE x₁ x)) (mulE (mulE x₂ x₁) x)

  emptySubLemma : ∀ {Γ Δ} → Γ ⊢s Δ → Δ empty → Γ empty
  emptySubLemma emptySub empt = empt
  emptySubLemma var ()
  emptySubLemma (comma sub sub₁) (mulE empt empt₁) = mulE (emptySubLemma sub empt) (emptySubLemma sub₁ empt₁)
  emptySubLemma (equiv x sub x₁) empt = lemma (emptySubLemma sub (lemma empt (sym x₁))) (sym x)

  lemmaSingleEmpty : ∀ {Γ A Δ} → Γ decTo sCtx A and Δ → · ≡ Δ → Γ ≡ sCtx A
  lemmaSingleEmpty SD empteq = decom SD SD empteq
  lemmaSingleEmpty (MD1 decpf) empteq = decom (MD1 decpf) SD (sym empteq)
  lemmaSingleEmpty (MD2 decpf) empteq = decom (MD2 decpf) SD (sym empteq)

  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂'
  dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) = · , · , emp (mulE x x) x , equiv (emp x x) emptySub (emp x x₁) , equiv (emp x x) emptySub (emp x x₂)
  dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
  dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom SD (MD1 x₁) eq) = sCtx A , · , decom (MD1 SD) SD (emp (mulE sinE sinE) sinE) , equiv refl var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv eq)))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv eq))
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom SD (MD2 x₁) eq) = · , sCtx A , decom (MD2 SD) SD (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv eq)) , equiv refl var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv eq))))
  dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) = · , · , emp (mulE sinE sinE) (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁)) , equiv (emp sinE sinE) emptySub (emp sinE x₂) , equiv (emp sinE sinE) emptySub (emp sinE x₃)
  dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (decom x x₁ pf) = {!!}
  dan Γ Γ' Γ₁' Γ₂' (equiv x sub x₁) pf with dan _ _ _ _ sub (trans x₁ pf)
  ... | Γ1 , Γ2 , split , sub1 , sub2 = Γ1 , Γ2 , trans split (sym x) , sub1 , sub2
