{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QfoundationZ45Zcore.Qpropositions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes

-- foundation-core.propositions.is-prop
d_is'45'prop_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'prop_8 = erased
-- foundation-core.propositions.UU-Prop
d_UU'45'Prop_14 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'Prop_14 = erased
-- foundation-core.propositions._.type-Prop
d_type'45'Prop_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'Prop_24 = erased
-- foundation-core.propositions._.is-prop-type-Prop
d_is'45'prop'45'type'45'Prop_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'type'45'Prop_30 ~v0 v1
  = du_is'45'prop'45'type'45'Prop_30 v1
du_is'45'prop'45'type'45'Prop_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'type'45'Prop_30 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation-core.propositions.is-prop-is-inhabited
d_is'45'prop'45'is'45'inhabited_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'inhabited_38 ~v0 ~v1 v2 v3 v4
  = du_is'45'prop'45'is'45'inhabited_38 v2 v3 v4
du_is'45'prop'45'is'45'inhabited_38 ::
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'inhabited_38 v0 v1 v2 = coe v0 v1 v1 v2
-- foundation-core.propositions._.all-elements-equal
d_all'45'elements'45'equal_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_all'45'elements'45'equal_54 = erased
-- foundation-core.propositions._.is-proof-irrelevant
d_is'45'proof'45'irrelevant_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'proof'45'irrelevant_60 = erased
-- foundation-core.propositions._.is-prop-all-elements-equal
d_is'45'prop'45'all'45'elements'45'equal_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'all'45'elements'45'equal_70 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'prop'45'all'45'elements'45'equal_70
du_is'45'prop'45'all'45'elements'45'equal_70 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'all'45'elements'45'equal_70
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- foundation-core.propositions._.eq-is-prop'
d_eq'45'is'45'prop''_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'is'45'prop''_82 = erased
-- foundation-core.propositions._.eq-is-prop
d_eq'45'is'45'prop_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'is'45'prop_94 = erased
-- foundation-core.propositions._.is-proof-irrelevant-all-elements-equal
d_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102 ~v0 ~v1
                                                            v2 v3
  = du_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102
      v2 v3
du_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v1) (coe v0 v1)
-- foundation-core.propositions._.is-proof-irrelevant-is-prop
d_is'45'proof'45'irrelevant'45'is'45'prop_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'proof'45'irrelevant'45'is'45'prop_112 ~v0 ~v1
  = du_is'45'proof'45'irrelevant'45'is'45'prop_112
du_is'45'proof'45'irrelevant'45'is'45'prop_112 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'proof'45'irrelevant'45'is'45'prop_112
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
      (coe
         (\ v0 ->
            coe du_is'45'proof'45'irrelevant'45'all'45'elements'45'equal_102))
      erased
-- foundation-core.propositions._.is-prop-is-proof-irrelevant
d_is'45'prop'45'is'45'proof'45'irrelevant_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'proof'45'irrelevant_114 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'prop'45'is'45'proof'45'irrelevant_114
du_is'45'prop'45'is'45'proof'45'irrelevant_114 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'proof'45'irrelevant_114
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416
-- foundation-core.propositions._.eq-is-proof-irrelevant
d_eq'45'is'45'proof'45'irrelevant_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'is'45'proof'45'irrelevant_122 = erased
-- foundation-core.propositions._.is-equiv-is-prop
d_is'45'equiv'45'is'45'prop_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'prop_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_is'45'equiv'45'is'45'prop_140 v7
du_is'45'equiv'45'is'45'prop_140 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'prop_140 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe v0) erased erased
-- foundation-core.propositions._.equiv-prop
d_equiv'45'prop_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'prop_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_equiv'45'prop_154 v6 v7
du_equiv'45'prop_154 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'prop_154 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) (coe du_is'45'equiv'45'is'45'prop_140 (coe v1))
-- foundation-core.propositions._.is-prop-is-equiv
d_is'45'prop'45'is'45'equiv_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'equiv_186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_is'45'prop'45'is'45'equiv_186
du_is'45'prop'45'is'45'equiv_186 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'equiv_186 v0 v1
  = coe du_is'45'prop'45'is'45'proof'45'irrelevant_114
-- foundation-core.propositions._.is-prop-equiv
d_is'45'prop'45'equiv_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'equiv_196 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'prop'45'equiv_196 v4
du_is'45'prop'45'equiv_196 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'equiv_196 v0
  = coe seq (coe v0) (\ v1 -> coe du_is'45'prop'45'is'45'equiv_186)
-- foundation-core.propositions._.is-prop-is-equiv'
d_is'45'prop'45'is'45'equiv''_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'equiv''_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_is'45'prop'45'is'45'equiv''_216
du_is'45'prop'45'is'45'equiv''_216 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'equiv''_216
  = coe du_is'45'prop'45'is'45'equiv_186
-- foundation-core.propositions._.is-prop-equiv'
d_is'45'prop'45'equiv''_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'equiv''_222 ~v0 ~v1 ~v2 ~v3 v4
  = du_is'45'prop'45'equiv''_222 v4
du_is'45'prop'45'equiv''_222 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'equiv''_222 v0
  = coe seq (coe v0) (\ v1 -> coe du_is'45'prop'45'is'45'equiv''_216)
-- foundation-core.propositions.is-prop-Σ
d_is'45'prop'45'Σ_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'Σ_238 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_is'45'prop'45'Σ_238 v4 v5 v6 v7
du_is'45'prop'45'Σ_238 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'Σ_238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QequalityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'eq'45'pair'45'Σ_104)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ''_356
         (coe
            v0
            (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
               (coe v2))
            (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
               (coe v3)))
         (coe
            (\ v4 ->
               coe
                 v1
                 (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                    (coe v3))
                 (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                    (coe v2))
                 (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                    (coe v3)))))
-- foundation-core.propositions.Σ-Prop
d_Σ'45'Prop_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_Σ'45'Prop_258 ~v0 ~v1 v2 v3 = du_Σ'45'Prop_258 v2 v3
du_Σ'45'Prop_258 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_Σ'45'Prop_258 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'prop'45'Σ_238
         (coe du_is'45'prop'45'type'45'Prop_30 (coe v0))
         (coe (\ v2 -> coe du_is'45'prop'45'type'45'Prop_30 (coe v1 v2))))
-- foundation-core.propositions.is-prop-prod
d_is'45'prop'45'prod_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'prod_280 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_is'45'prop'45'prod_280 v4 v5
du_is'45'prop'45'prod_280 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'prod_280 v0 v1
  = coe du_is'45'prop'45'Σ_238 (coe v0) (coe (\ v2 -> v1))
-- foundation-core.propositions.prod-Prop
d_prod'45'Prop_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_prod'45'Prop_292 ~v0 ~v1 v2 v3 = du_prod'45'Prop_292 v2 v3
du_prod'45'Prop_292 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_prod'45'Prop_292 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'prop'45'prod_280
         (coe du_is'45'prop'45'type'45'Prop_30 (coe v0))
         (coe du_is'45'prop'45'type'45'Prop_30 (coe v1)))
