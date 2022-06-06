{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QbinaryZ45Zrelations

-- foundation.equivalence-relations.is-equivalence-relation
d_is'45'equivalence'45'relation_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_is'45'equivalence'45'relation_12 = erased
-- foundation.equivalence-relations.Eq-Rel
d_Eq'45'Rel_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_Eq'45'Rel_22 = erased
-- foundation.equivalence-relations.prop-Eq-Rel
d_prop'45'Eq'45'Rel_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_prop'45'Eq'45'Rel_34 ~v0 ~v1 ~v2 = du_prop'45'Eq'45'Rel_34
du_prop'45'Eq'45'Rel_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_prop'45'Eq'45'Rel_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
-- foundation.equivalence-relations.type-Eq-Rel
d_type'45'Eq'45'Rel_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> ()
d_type'45'Eq'45'Rel_42 = erased
-- foundation.equivalence-relations.is-prop-type-Eq-Rel
d_is'45'prop'45'type'45'Eq'45'Rel_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'type'45'Eq'45'Rel_58 ~v0 ~v1 ~v2 v3
  = du_is'45'prop'45'type'45'Eq'45'Rel_58 v3
du_is'45'prop'45'type'45'Eq'45'Rel_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'type'45'Eq'45'Rel_58 v0
  = coe
      MAlonzo.Code.Qfoundation.QbinaryZ45Zrelations.du_is'45'prop'45'type'45'Rel'45'Prop_56
      (coe du_prop'45'Eq'45'Rel_34 v0)
-- foundation.equivalence-relations.is-equivalence-relation-prop-Eq-Rel
d_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 ~v0 ~v1 ~v2
                                                        v3
  = du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 v3
du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.equivalence-relations.refl-Eq-Rel
d_refl'45'Eq'45'Rel_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_refl'45'Eq'45'Rel_82 ~v0 ~v1 ~v2 v3 v4
  = du_refl'45'Eq'45'Rel_82 v3 v4
du_refl'45'Eq'45'Rel_82 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_refl'45'Eq'45'Rel_82 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 (coe v0))
      v1
-- foundation.equivalence-relations.symm-Eq-Rel
d_symm'45'Eq'45'Rel_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_symm'45'Eq'45'Rel_94 ~v0 ~v1 ~v2 v3 v4 v5
  = du_symm'45'Eq'45'Rel_94 v3 v4 v5
du_symm'45'Eq'45'Rel_94 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_symm'45'Eq'45'Rel_94 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe
            du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 (coe v0)))
      v1 v2
-- foundation.equivalence-relations.equiv-symm-Eq-Rel
d_equiv'45'symm'45'Eq'45'Rel_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'symm'45'Eq'45'Rel_110 ~v0 ~v1 ~v2 v3 v4 v5
  = du_equiv'45'symm'45'Eq'45'Rel_110 v3 v4 v5
du_equiv'45'symm'45'Eq'45'Rel_110 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'symm'45'Eq'45'Rel_110 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_equiv'45'prop_154
      (coe du_symm'45'Eq'45'Rel_94 (coe v0) (coe v1) (coe v2))
      (coe du_symm'45'Eq'45'Rel_94 (coe v0) (coe v2) (coe v1))
-- foundation.equivalence-relations.trans-Eq-Rel
d_trans'45'Eq'45'Rel_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'45'Eq'45'Rel_126 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_trans'45'Eq'45'Rel_126 v3 v4 v5 v6
du_trans'45'Eq'45'Rel_126 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans'45'Eq'45'Rel_126 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe
            du_is'45'equivalence'45'relation'45'prop'45'Eq'45'Rel_70 (coe v0)))
      v1 v2 v3
