(** This module proves the fundamental property of the logical
relation defined in the [LogicalRelation] module. *)

From Rattus Require Import Tactics.

From Rattus Require Export LogicalRelationAux.

From Coq Require Import Program.Equality Arith.Wf_nat Omega.


Theorem fund_prop nu ty (G : ctx ty) t A Hs s g :
  hastype G t A -> crel nu G Hs s g -> closed_sub g ->
  closed_heapseq Hs -> closed_store s ->
  trel nu A Hs s (sub_app g t).
Proof.
  intros T. generalize dependent g. generalize dependent Hs. generalize dependent nu.
  generalize dependent s. 
  induction T;  intros s nu Hs g C CS CH Cs.
  - (* unit *)
    apply vrel_trel. simpl. autorewrite with vrel. auto.
  - (* natlit *)
    apply vrel_trel. simpl. autorewrite with vrel. eauto.
  - (* add *)
    unfold trel in *. intros s' TL HCs.
    assert (exists (v : term) (s'' : store), {sub_app g t1, s'}⇓ {v, s''} /\ vrel nu Nat Hs s'' v)
      as IH1 by (eapply IHT1;eauto).
    autorewrite with vrel' in IH1.
    destruct IH1 as (v1 & s'' & R1 & n & V1). subst.
    assert (exists (v : term) (s''' : store), {sub_app g t2, s''}⇓ {v, s'''}
                                              /\ vrel nu Nat Hs s''' v) as IH2.
    eapply IHT2;eauto.
    eauto using tick_le_trans,red_extensive,tick_le_store.
    eapply red_closed_store; try eassumption. eauto using crel_sub_closed.
    autorewrite with vrel' in IH2.
    destruct IH2 as (v2 & s''' & R2 & m & V2). subst.
    exists (natlit (n + m)). exists s'''. split. simpl. eauto.
    autorewrite with vrel'. eauto.
  - (* var *)
    eapply ctx_lookup_vrel in H; try eassumption. autodest.
    apply vrel_trel. simpl. rewrite H. assumption.
  - (* abs *)
    apply vrel_trel. simpl. autorewrite with vrel'.
    exists (sub_app (None :: g) t). split. reflexivity.
    intros. rewrite sub_term_merge.
    apply IHT. constructor. assumption.
    apply crel_gc in C. eauto using crel_mono. 
    auto. auto. auto. auto.
  - (* app *)
    apply trel_app with (T1:=T1); eauto using crel_sub_closed.
  - (* pair *)
    unfold trel in *. intros s' TL HCs.
   
    assert (exists (v : term) (s'' : store),
               {sub_app g t1, s'}⇓ {v, s''} /\ vrel nu T1 Hs s'' v) as IH1 by
          (eapply IHT1; eauto).
    destruct IH1 as (v & s'' & R1 & V1).
    assert (closed_term (sub_app g t1)) as CT by eauto using crel_sub_closed.
    pose (red_closed _ _ _ _ CT HCs R1) as MC.
    destruct MC as [CV Cs'].
    pose (red_extensive _ _ _ _ R1) as Ex1.
    apply tick_le_store in Ex1.
    assert (exists (v' : term) (s''' : store),
               {sub_app g t2, s''}⇓ {v', s'''} /\ vrel nu T2 Hs s''' v') as IH2 by
          (eapply IHT2; eauto using tick_le_trans).
    destruct IH2 as (v' & s''' & R2 & V2).

    pose (red_extensive _ _ _ _ R2) as Ex2.
    apply tick_le_store in Ex2.
    eexists. eexists. simpl. split. eapply red_pair;eauto.
    rewrite vrel_times. eexists. eexists.
    split. reflexivity.  eauto using vrel_mono.
  - (* pr1 *)
    unfold trel in *. intros s' TL HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel nu (Times T1 T2) Hs s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).
    rewrite vrel_times in V. autodest.
    eexists. eexists. split. simpl. eapply red_pr1. eassumption. assumption.
     
  - (* pr2 *)
    unfold trel in *. intros s' TL HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel nu (Times T1 T2) Hs s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).
    rewrite vrel_times in V. autodest.
    eexists. eexists. split. simpl. eapply red_pr2. eassumption. assumption.
  - (* in1 *)
    unfold trel in *. intros s' TL HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel nu T1 Hs s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).

    eexists. eexists. split. simpl. eapply red_in1. eassumption.
    rewrite vrel_plus. eauto.
    
  - (* in2 *)
    unfold trel in *. intros s' TL HCs.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel nu T2 Hs s'' v) as IH by
          (eapply IHT; eauto).
    destruct IH as (v & s'' & R & V).

    eexists. eexists. split. simpl. eapply red_in2. eassumption.
    rewrite vrel_plus. eauto.
  - (* case *)
    simpl. unfold trel in *. intros s' TL HCs.
   
    assert (exists (v : term) (s'' : store),
         {sub_app g t, s'}⇓ {v, s''} /\ vrel nu (Plus T2 T3) Hs s'' v) as IH1 by
          (eapply IHT1; eauto).
    destruct IH1 as (v & s'' & R1 & V1). clear IHT1.
    assert (closed_term (sub_app g t)) as CT by eauto using crel_sub_closed.
    pose (red_closed _ _ _ _ CT HCs R1) as MC.
    destruct MC as [CV Cs'].
    pose (red_extensive _ _ _ _ R1) as Ex1.
    apply tick_le_store in Ex1.
    rewrite vrel_plus in V1.
    destruct V1 as [V1|V1]; destruct V1 as (v0 & Subst & V1);subst.
    + inversion CV. subst.
      assert (exists (v' : term) (s''' : store),
                 {sub_app (Some v0 :: g) t1, s''}⇓ {v', s'''} /\ vrel nu T1 Hs s''' v') as IH2 by
            (eapply IHT2; eauto using tick_le_trans, crel_var,crel_mono).

      destruct IH2 as (v' & s''' & R2 & V2).
          
      pose (red_extensive _ _ _ _ R2) as Ex2.
      apply tick_le_store in Ex2.
    
      eexists. eexists. split. simpl. 
      eapply red_case1; try eassumption. rewrite sub_term_merge. eassumption. assumption.
      assumption.
    + inversion CV. subst.
      assert (exists (v' : term) (s''' : store),
                 {sub_app (Some v0 :: g) t2, s''}⇓ {v', s'''} /\ vrel nu T1 Hs s''' v') as IH2 by
            (eapply IHT3; eauto using tick_le_trans, crel_var,crel_mono).

      destruct IH2 as (v' & s''' & R2 & V2).
          
      pose (red_extensive _ _ _ _ R2) as Ex2.
      apply tick_le_store in Ex2.
    
      eexists. eexists. split. simpl. 
      eapply red_case2; try eassumption. rewrite sub_term_merge. eassumption. assumption.
      assumption.
    
  - (* delay *)
    unfold trel. intros s' TL Cs'.
    apply crel_mono with (Hs':=cons (hd Hs) (tl Hs)) (s':=s') (nu' := nu) in C;
      auto using closed_heapseq_tail, closed_heapseq_head, closed_heapseq_cons.
    destruct s' as (h&h'). 
    eexists. eexists. simpl. split.
    apply red_delay; eauto.
    destruct nu.
    + rewrite vrel_delay_nil. eauto.
    + rewrite vrel_delay. eexists. eexists. split. reflexivity.
      split. apply store_mapsto_cons.
      (* dependent destruction CHs'. *)
      (* intros. *)
      
      apply crel_gc in C;try solve[intro CO;inversion CO].

      apply crel_tick in C.
      apply IHT in C;eauto using closed_heapseq_tail, closed_heapseq_head, closed_store_now.
      simpl. eapply trel_mono; try apply C;
      eauto using heap_fresh_alloc,heap_cons_mono.

  - (* adv *)
    (* assert (exists hn hl : heap, s = (Some hn, hl)) as S by eauto using crel_later. *)
    (* destruct S as (hn&hl&S). subst. *)
    (* apply trel_adv. *)
    unfold trel in *. intros s' TL Cs'.
    assert (exists hn hl : heap, s = (Some hn, hl)) as S by eauto using crel_later.
    destruct S as (hn&hl&S). subst.
    
    pose (tick_le_tick' _ _ _ TL) as ST.
    destruct ST as (hn' & hl' & [ST [HLn HLl]]). subst.
    dependent destruction Cs.
    dependent destruction Cs'.
    assert (exists (v : term) (s'' : store),
       {sub_app (sub_skip (skip_later_count G) g) t, (None, hn') }⇓ {v, s''} /\
       vrel (S nu) (Delay T) (cons hl Hs) s'' v) as IH by
          (eapply IHT;eauto using crel_skip_later, sub_skip_closed).
    destruct IH as (v & s''& R & V).
    assert (store_le (None, hn') (s'')) as SL
        by eauto using red_extensive.
    inversion SL. subst.
    rewrite vrel_delay in V.
    destruct V as (l & u & [RL [M TT]]). subst.
    assert (closed_term (ref l) /\ closed_store (None, h')) as CL by
          (eapply red_closed; try eassumption;
           eauto using crel_sub_closed, sub_skip_closed, crel_skip_later).
    destruct CL as [CL1 CL2].
    dependent destruction CL2.
    unfold trel in TT.
    assert (exists (v : term) (s'' : store),
               {u, (Some h', hl')}⇓ {v, s''} /\
               vrel nu T Hs s'' v) as TT' by
          (eapply TT ; simpl;eauto using crel_skip_later, sub_skip_closed).
    destruct TT' as (v & s'' & R2 & V2).
    erewrite sub_skip_later_app in R by eauto.
    
    simpl. exists v, s''. split. eapply red_adv. eapply R.
    inversion M;subst. eassumption. eassumption. auto. 

  - (* box *)
    apply vrel_trel. simpl. autorewrite with vrel'.
    exists (sub_app g t). split. auto. intros Hs' Hs0C.

    eapply crel_stabilize with (Hs' := Hs') (s' := (None, heap_empty)) in C;
      eauto using closed_heap_empty.
    apply IHT in C;eauto using closed_heap_empty, sub_skipc_closed.

    erewrite sub_skipc_id in C by eassumption. assumption.

  - (* unbox *)
    unfold trel in *. intros s' TL Cs'.
    apply crel_mono with (Hs':=Hs) (s':=s') (nu':=nu) in C;auto.

    assert (exists (v : term) (s'' : store), {sub_app g t, s'}⇓ {v, s''} /\ vrel nu (Box T) Hs s'' v) as IH.

    eapply IHT; try eauto.
    destruct IH as (v&s''&R&V).
    rewrite vrel_box in V.
    destruct V as (t' & E & IH). subst.
    unfold trel in *.

    assert (exists (v : term) (s''' : store), {t', s''}⇓ {v, s'''} /\ vrel nu T Hs s''' v) as V'.
    apply IH;eauto using tick_le_empty. 
    eapply red_closed_store. eapply crel_sub_closed;eassumption. eassumption. eassumption.


    destruct V' as (v & s''' & R' & V). 
    exists v. exists s'''. split. simpl. eauto. eauto.
  - (* fixp *)
    assert (closed_term (sub_app g (fixp t))) as CF by
    (eapply crel_sub_closed;eauto).
    
    assert (forall Hs' s', closed_heapseq Hs' -> closed_store s' ->
                           crel nu (stabilize G) Hs' s' (sub_skipc (stabilize G) g)) as C'
      by eauto using crel_stabilize.
    clear C.
    
    simpl in *.
    generalize dependent s. generalize dependent Hs.
    induction (lt_wf nu) as [nu _ IH]. intros.

    intros s' TL Cs'. destruct s' as (hn&hl).     remember (alloc_fresh hl) as l.
    assert (forall Hs', closed_heapseq Hs' -> vrel nu (Delay T) Hs' (hn, heap_cons hl l (fixp (sub_app (None :: g) t))) (ref l)) as DE. intros Hs' CHs'.
    destruct nu.
    + rewrite vrel_delay_nil. eauto.
    + rewrite vrel_delay. eexists. eexists.
      split. auto. split. auto using store_mapsto_cons.
      apply IH;eauto using closed_heapseq_tail,crel_mono, C'. 
      simpl. eauto using closed_store_now, closed_heap_alloc, closed_heapseq_head.
    + 


      assert (exists v s'', {sub_app (Some (ref (alloc_fresh hl))::(sub_skipc (stabilize G) g)) t ,
  (hn, heap_cons hl (alloc_fresh hl) (fixp (sub_app (None :: (sub_skipc (stabilize G) g)) t)))}⇓ {
                                                                                                 v, s''} /\  vrel nu T Hs s'' v). eapply IHT.
      constructor. rewrite <- Heql. eapply DE. eauto using closed_heapseq_tail.
      eapply C';eauto using closed_heapseq_tail, closed_store_cons.
      eauto using sub_skipc_closed. eauto using closed_heapseq_tail.
      eauto using closed_store_cons. subst.
      erewrite <- sub_skipc_id with (G := ctx_var (stabilize G) (Delay T));eauto.
      erewrite <- sub_skipc_id with (G := ctx_var (stabilize G) (Delay T)) in CF;
        eauto using closed_store_cons.

      destruct H as (v & s'' & R & V). eexists. eexists. split.
      apply red_fix. erewrite <- sub_skipc_id  with (G := ctx_var (stabilize G) (Delay T));eauto.
      simpl. rewrite sub_term_merge. eassumption. eauto using sub_skipc_closed. assumption.
  - (* into *)
    unfold trel in *. intros s' TL Cs'.
    apply crel_mono with (Hs':=Hs) (s':=s') (nu' := nu) in C;auto.
    assert (exists (v : term) (s'' : store),
               {sub_app g t, s'}⇓ {v, s''} /\ vrel nu (tsubst 0 T (Delay (Fix T))) Hs s'' v) as IH
        by (eapply IHT;try eassumption;eauto).
    destruct IH as (v & s''& R & V).
    eexists. eexists. split. simpl. apply red_into. apply R.
    rewrite vrel_mu. eauto.
  - (* out *)
    unfold trel in *. intros s' TL Cs'.
    apply crel_mono with (Hs':=Hs) (s':=s') (nu' := nu) in C;auto.
    assert (exists (v : term) (s'' : store), {sub_app g t, s'}⇓ {v, s''}
                                             /\ vrel nu (Fix A) Hs s'' v) as IH
        by (eapply IHT;try eassumption;eauto).
    destruct IH as (v & s''& R & V).
    rewrite vrel_mu in V.
    destruct V as (v' & E & V). subst.
    eexists. eexists. split. simpl. apply red_out. apply R. apply V.
Qed.


Corollary fund_prop_closed nu t A Hs s :
  hastype ctx_empty t A -> closed_heapseq Hs -> closed_store s ->
  trel nu A Hs s t.
Proof.
  intros Ty CHs Cs. erewrite <- sub_empty_app. eapply fund_prop;eauto. auto.
Qed. 
