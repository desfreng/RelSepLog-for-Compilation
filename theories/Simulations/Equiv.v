From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations.Equiv Require Import FSimToGSim GSimToEAltSim EAltSimToESimLax.
From RSL.Simulations.Equiv Require Import ESimLaxToESim ISimToFSim ESimToISim.
From RSL.Simulations.Equiv Require Import CCSimEquivCCSimAlt CCSimAltEquivESimLax.

Section EQ.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs) (ϕ: post Λt Λs).

  Lemma isim_to_fsim {J I: WfRel} t s :
    isim Et Es ϕ t s ->
    ∀ (j Tj: J) (i Ti: I),
    j ⊏ Tj ->
    i ⊏ Ti ->
    fsim _ _ Et Es ϕ t j i s.
  Proof using Type. by apply isim_implies_fsim. Qed.

  Lemma esim_to_isim {W: WfRel} (i: W) t s :
    esim _ Et Es ϕ i t s -> isim Et Es ϕ t s.
  Proof using Type. by apply esim_implies_isim. Qed.

  Lemma fsim_to_esim {J I: WfRel}:
    ∀ (j: J) t (i: I) s,
    fsim _ _ Et Es ϕ t j i s ->
    ∃ (W: WfRel) (i: W), esim W Et Es ϕ i t s.
  Proof using Type.
    intros j t i s Hsim.
    apply fsim_implies_gsim in Hsim.
    destruct Hsim as (wt & ws & Hgsim).
    eexists _, _.
    eapply esim_lax_implies_esim_inv. { by apply nsteps_refl. }
    apply ealt_sim_implies_esim_lax.
    by apply gsim_implies_ealt_sim.
  Qed.

  Lemma index_irrel
    {J J' I I': WfRel} `{NoIsolatedElements J'} `{NoIsolatedElements I'}:
    ∀ (j: J) t (i: I) s,
    fsim _ _ Et Es ϕ t j i s ->
    ∀ (j': J') (i': I'),
    fsim _ _ Et Es ϕ t j' i' s.
  Proof using Type.
    intros j t i s Hsim.
    apply fsim_to_esim in Hsim.
    destruct Hsim as (W & x & Hsim).
    eapply esim_to_isim in Hsim.
    clear W x i j.
    intros j' i'.
    destruct (no_isolated j') as [jj [ Hltj | Hgtj ]];
      destruct (no_isolated i') as [ii [ Hlti | Hlti ]];
      (eapply chain_mono;
       [ firstorder | | | eapply isim_to_fsim; eassumption ]; easy || now left).
  Qed.

  Theorem fsim_same_as_bool (J I: WfRel) :
    Inhabited J ->
    Inhabited I ->
    NoIsolatedElements J ->
    NoIsolatedElements I ->
    ∀ t s,
    (∃ (j: J) (i: I), fsim _ _ Et Es ϕ t j i s)
    <->
    (∃ j i : bool, fsim _ _ Et Es ϕ t j i s).
  Proof using Type.
    intros HInJ HInI HIsoJ HIsoI t s.
    split; intros (j & i & Hsim).
    - exists true, true.
      eapply index_irrel.
      eassumption.
    - destruct HInJ as [jj].
      destruct HInI as [ii].
      exists jj, ii.
      eapply index_irrel.
      eassumption.
  Qed.

End EQ.
