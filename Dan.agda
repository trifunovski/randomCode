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

  data _empty : Ctx → Set where
    sinE : · empty
    mulE : ∀ {Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → (Γ₁ , Γ₂) empty

  data _single_ : Tp → Ctx → Set where
    sinT : ∀{A} → A single (sCtx A)
    mulT1 : ∀{Γ₁ Γ₂ A} → A single Γ₁ → Γ₂ empty → A single (Γ₁ , Γ₂)
    mulT2 : ∀{Γ₁ Γ₂ A} → Γ₁ empty → A single Γ₂ → A single (Γ₁ , Γ₂)

  data _≡_ : Ctx → Ctx → Set where
    refl : ∀{Γ} → Γ ≡ Γ
    emp : ∀{Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → Γ₁ ≡ Γ₂
    leaf : ∀{A Γ₁ Γ₂} → A single Γ₁ → A single Γ₂ → Γ₁ ≡ Γ₂
    node : ∀{Γ₁ Γ₂ Δ₁ Δ₂} → Either (Γ₁ ≡ Δ₁ × Γ₂ ≡ Δ₂)
                                   (Γ₁ ≡ Δ₂ × Γ₂ ≡ Δ₁)
                          → (Γ₁ , Γ₂) ≡ (Δ₁ , Δ₂)

  data _⊢s_ : Ctx → Ctx → Set where
    emptySub : · ⊢s ·
    var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
    comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
    equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ

  canthappen : ∀{A Γ} → Γ empty → A single Γ → Void
  canthappen sinE ()
  canthappen (mulE empt empt₁) (mulT1 sin x) = canthappen empt sin
  canthappen (mulE empt empt₁) (mulT2 x sin) = canthappen empt₁ sin

  sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
  sym {·} {·} refl = refl
  sym {·} {·} (emp x x₁) = refl
  sym {·} {·} (leaf x x₁) = refl
  sym {·} {sCtx x} (emp x₁ ())
  sym {·} {sCtx x} (leaf x₁ sinT) = leaf sinT x₁
  sym {·} {Γ₂ , Γ₃} (emp x x₁) = emp x₁ x
  sym {·} {Γ₂ , Γ₃} (leaf () x₁)
  sym {sCtx x} {·} (emp () x₂)
  sym {sCtx x} {·} (leaf x₁ ())
  sym {sCtx x} {sCtx .x} refl = refl
  sym {sCtx x} {sCtx x₁} (emp () x₃)
  sym {sCtx x} {sCtx x₁} (leaf x₂ x₃) = leaf x₃ x₂
  sym {sCtx x} {Γ₂ , Γ₃} (emp () x₂)
  sym {sCtx x} {Γ₂ , Γ₃} (leaf x₁ x₂) = leaf x₂ x₁
  sym {Γ₁ , Γ₂} {·} (emp x x₁) = emp x₁ x
  sym {Γ₁ , Γ₂} {·} (leaf x ())
  sym {Γ₁ , Γ₂} {sCtx x} (emp x₁ ())
  sym {Γ₁ , Γ₂} {sCtx x} (leaf x₁ x₂) = leaf x₂ x₁
  sym {Γ₁ , Γ₂} {.Γ₁ , .Γ₂} refl = refl
  sym {Γ₁ , Γ₂} {Γ₃ , Γ₄} (emp x x₁) = emp x₁ x
  sym {Γ₁ , Γ₂} {Γ₃ , Γ₄} (leaf x x₁) = leaf x₁ x
  sym {Γ₁ , Γ₂} {Γ₃ , Γ₄} (node (Inl (fst , snd))) = node (Inl (sym fst , sym snd))
  sym {Γ₁ , Γ₂} {Γ₃ , Γ₄} (node (Inr (fst , snd))) = node (Inr (sym snd , sym fst))

  lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
  lemma sinE refl = sinE
  lemma sinE (emp x x₁) = x₁
  lemma sinE (leaf () x₁)
  lemma (mulE empty empty₁) refl = mulE empty empty₁
  lemma (mulE empty empty₁) (emp x x₁) = x₁
  lemma (mulE empty empty₁) (leaf (mulT1 x x₁) x₂) = abort (canthappen empty x)
  lemma (mulE empty empty₁) (leaf (mulT2 x x₁) x₂) = abort (canthappen empty₁ x₁)
  lemma (mulE empty empty₁) (node (Inl (fst , snd))) = mulE (lemma empty fst) (lemma empty₁ snd)
  lemma (mulE empty empty₁) (node (Inr (fst , snd))) = mulE (lemma empty₁ snd) (lemma empty fst)

  lemmaAB : ∀{A B Γ Δ} → A single Γ → B single Γ → B single Δ → A single Δ
  lemmaAB sinT sinT s3 = s3
  lemmaAB (mulT1 s1 x) (mulT1 s2 x₁) s3 = lemmaAB s1 s2 s3
  lemmaAB (mulT1 s1 x) (mulT2 x₁ s2) s3 = abort (canthappen x₁ s1)
  lemmaAB (mulT2 x s1) (mulT1 s2 x₁) s3 = abort (canthappen x₁ s1)
  lemmaAB (mulT2 x s1) (mulT2 x₁ s2) s3 = lemmaAB s1 s2 s3

  lemmaSin : ∀{Γ Δ A} → A single Γ → Γ ≡ Δ → A single Δ
  lemmaSin sinT refl = sinT
  lemmaSin sinT (emp () x₁)
  lemmaSin sinT (leaf sinT x₁) = x₁
  lemmaSin (mulT1 sing x) refl = mulT1 sing x
  lemmaSin (mulT1 sing x) (emp (mulE x₁ x₂) x₃) = abort (canthappen x₁ sing)
  lemmaSin (mulT1 sing x) (leaf (mulT1 x₁ x₂) x₃) = lemmaAB sing x₁ x₃
  lemmaSin (mulT1 sing x) (leaf (mulT2 x₁ x₂) x₃) = abort (canthappen x₁ sing)
  lemmaSin (mulT1 sing x) (node (Inl (fst , snd))) = mulT1 (lemmaSin sing fst) (lemma x snd)
  lemmaSin (mulT1 sing x) (node (Inr (fst , snd))) = mulT2 (lemma x snd) (lemmaSin sing fst)
  lemmaSin (mulT2 x sing) refl = mulT2 x sing
  lemmaSin (mulT2 x sing) (emp (mulE x₁ x₂) x₃) = abort (canthappen x₂ sing)
  lemmaSin (mulT2 x sing) (leaf (mulT1 x₁ x₂) x₃) = abort (canthappen x₂ sing)
  lemmaSin (mulT2 x sing) (leaf (mulT2 x₁ x₂) x₃) = lemmaAB sing x₂ x₃
  lemmaSin (mulT2 x sing) (node (Inl (fst , snd))) = mulT2 (lemma x fst) (lemmaSin sing snd)
  lemmaSin (mulT2 x sing) (node (Inr (fst , snd))) = mulT1 (lemmaSin sing snd) (lemma x fst)

  trans : ∀{Γ₁ Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ ≡ Γ₃
  trans refl pf = pf
  trans (emp x x₁) refl = emp x x₁
  trans (emp x x₁) (emp x₂ x₃) = emp x x₃
  trans {Γ₂ = ·} (emp x x₁) (leaf () x₃)
  trans {Γ₂ = sCtx x} (emp x₁ ()) (leaf x₃ x₄)
  trans {Γ₂ = Γ₂ , Γ₃} (emp x x₂) (leaf x₃ x₄) = abort (canthappen x₂ x₃)
  trans (emp x (mulE x₁ x₂)) (node (Inl (fst , snd))) = emp x (mulE (lemma x₁ fst) (lemma x₂ snd))
  trans (emp x (mulE x₁ x₂)) (node (Inr (fst , snd))) = emp x (mulE (lemma x₂ snd) (lemma x₁ fst))
  trans (leaf x x₁) refl = leaf x x₁
  trans (leaf x x₁) (emp x₂ x₃) = abort (canthappen x₂ x₁)
  trans (leaf x x₁) (leaf x₂ x₃) = leaf x (lemmaAB x₁ x₂ x₃)
  trans (leaf x (mulT1 x₁ x₂)) (node (Inl (fst , snd))) = leaf x (mulT1 (lemmaSin x₁ fst) (lemma x₂ snd))
  trans (leaf x (mulT2 x₁ x₂)) (node (Inl (fst , snd))) = leaf x (mulT2 (lemma x₁ fst) (lemmaSin x₂ snd))
  trans (leaf x (mulT1 x₁ x₂)) (node (Inr (fst , snd))) = leaf x (mulT2 (lemma x₂ snd) (lemmaSin x₁ fst))
  trans (leaf x (mulT2 x₁ x₂)) (node (Inr (fst , snd))) = leaf x (mulT1 (lemmaSin x₂ snd) (lemma x₁ fst))
  trans (node x) refl = node x
  trans (node (Inl (fst , snd))) (emp (mulE x₁ x₂) x₃) = emp (mulE (lemma x₁ (sym fst)) (lemma x₂ (sym snd))) x₃
  trans (node (Inr (fst , snd))) (emp (mulE x₁ x₂) x₃) = emp (mulE (lemma x₂ (sym fst)) (lemma x₁ (sym snd))) x₃
  trans (node (Inl (fst , snd))) (leaf (mulT1 x₁ x) x₂) = leaf (mulT1 (lemmaSin x₁ (sym fst)) (lemma x (sym snd))) x₂
  trans (node (Inl (fst , snd))) (leaf (mulT2 x x₁) x₂) = leaf (mulT2 (lemma x (sym fst)) (lemmaSin x₁ (sym snd))) x₂
  trans (node (Inr (fst , snd))) (leaf (mulT1 x₁ x₂) x₃) = leaf (mulT2 (lemma x₂ (sym fst)) (lemmaSin x₁ (sym snd))) x₃
  trans (node (Inr (fst , snd))) (leaf (mulT2 x₁ x₂) x₃) = leaf (mulT1 (lemmaSin x₂ (sym fst)) (lemma x₁ (sym snd))) x₃
  trans (node (Inl (fst , snd))) (node (Inl (fst₁ , snd₁))) = node (Inl ((trans fst fst₁) , trans snd snd₁))
  trans (node (Inl (fst , snd))) (node (Inr (fst₁ , snd₁))) = node (Inr ((trans fst fst₁) , (trans snd snd₁)))
  trans (node (Inr (fst , snd))) (node (Inl (fst₁ , snd₁))) = node (Inr (trans fst snd₁ , trans snd fst₁))
  trans (node (Inr (fst , snd))) (node (Inr (fst₁ , snd₁))) = node (Inl ((trans fst snd₁) , (trans snd fst₁)))

  comm : ∀{Γ₁ Γ₂} → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
  comm {Γ₁}{Γ₂} = node (Inr (refl , refl))

  -- assoc : ∀{Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
  -- assoc {Γ₁}{Γ₂}{Γ₃} = {!!}

  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂'
  dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) = · , · , emp (mulE x x) x , equiv refl emptySub (emp x x₁) , equiv refl emptySub (emp x x₂)
  dan .· .· Γ₁' Γ₂ emptySub (leaf () (mulT1 x₁ x₂))
  dan .· .· Γ₁' Γ₂ emptySub (leaf () (mulT2 x₁ x₂))
  dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
  dan ._ ._ Γ₁' Γ₂ var (leaf {A} x (mulT1 x₁ x₂)) = sCtx A , · , leaf (mulT1 sinT sinE) x , equiv refl var (leaf sinT x₁) , equiv refl emptySub (emp sinE x₂)
  dan ._ ._ Γ₁' Γ₂ var (leaf {A} x (mulT2 x₁ x₂)) = · , sCtx A , leaf (mulT2 sinE sinT) x , equiv refl emptySub (emp sinE x₁) , equiv refl var (leaf sinT x₂)
  dan ._ .(Γ₁' , Γ₂') Γ₁' Γ₂' (comma {Γ₁}{Γ₂} sub sub₁) refl = Γ₁ , Γ₂ , refl , sub , sub₁
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) = Γ₁ , Γ₂ , refl , equiv refl sub (emp x x₂) , equiv refl sub₁ (emp x₁ x₃)
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub sub₁) (leaf {A} (mulT1 x x₁) (mulT1 x₂ x₃)) = Γ₁ , Γ₂ , refl , equiv refl sub (leaf x x₂) , equiv refl sub₁ (emp x₁ x₃)
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub sub₁) (leaf {A} (mulT1 x x₁) (mulT2 x₂ x₃)) = Γ₂ , Γ₁ , comm , equiv refl sub₁ (emp x₁ x₂) , equiv refl sub (leaf x x₃)
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub sub₁) (leaf {A} (mulT2 x x₁) (mulT1 x₂ x₃)) = Γ₂ , Γ₁ , comm , equiv refl sub₁ (leaf x₁ x₂) , equiv refl sub (emp x x₃)
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub sub₁) (leaf {A} (mulT2 x x₁) (mulT2 x₂ x₃)) = Γ₁ , Γ₂ , refl , equiv refl sub (emp x x₂) , equiv refl sub₁ (leaf x₁ x₃)
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub₁ sub) (node (Inl (fst , snd))) = Γ₁ , Γ₂ , refl , equiv refl sub₁ fst , equiv refl sub snd
  dan ._ ._ Γ₁' Γ₂' (comma{Γ₁}{Γ₂} sub₁ sub) (node (Inr (fst , snd))) = Γ₂ , Γ₁ , comm , equiv refl sub snd , equiv refl sub₁ fst
  dan Γ Γ' Γ₁' Γ₂' (equiv x sub x₁) pf with dan _ _ _ _ sub (trans x₁ pf)
  ... | Γ1 , Γ2 , split , sub1 , sub2 = Γ1 , Γ2 , trans split (sym x) , sub1 , sub2
