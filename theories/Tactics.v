Ltac autodest := match goal with
                 | [H : exists _ : _, _ |- _] => destruct H; autodest
                 | [H : _ /\ _ |- _] => destruct H; autodest
                 | [H : _ \/ _ |- _] => destruct H; autodest
                 | [H : False |- _] => inversion H
                 | _ => subst;eauto
                end.
