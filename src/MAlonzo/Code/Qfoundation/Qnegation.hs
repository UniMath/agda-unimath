{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.Qnegation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences
import qualified MAlonzo.Code.Qfoundation.Qpropositions

-- foundation.negation.is-prop-neg
d_is'45'prop'45'neg_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'neg_8 v0 ~v1 = du_is'45'prop'45'neg_8 v0
du_is'45'prop'45'neg_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'neg_8 v0
  = coe
      MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'function'45'type_192
      v0 ()
      (\ v1 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_is'45'prop'45'empty_88)
-- foundation.negation.neg-Prop'
d_neg'45'Prop''_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_neg'45'Prop''_14 v0 ~v1 = du_neg'45'Prop''_14 v0
du_neg'45'Prop''_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_neg'45'Prop''_14 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'neg_8 (coe v0))
-- foundation.negation.neg-Prop
d_neg'45'Prop_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_neg'45'Prop_22 v0 ~v1 = du_neg'45'Prop_22 v0
du_neg'45'Prop_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_neg'45'Prop_22 v0 = coe du_neg'45'Prop''_14 (coe v0)
-- foundation.negation.reductio-ad-absurdum
d_reductio'45'ad'45'absurdum_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny
d_reductio'45'ad'45'absurdum_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_reductio'45'ad'45'absurdum_34
du_reductio'45'ad'45'absurdum_34 :: AgdaAny
du_reductio'45'ad'45'absurdum_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.du_ex'45'falso_18
      erased
-- foundation.negation.equiv-neg
d_equiv'45'neg_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'neg_48 ~v0 ~v1 ~v2 ~v3 ~v4 = du_equiv'45'neg_48
du_equiv'45'neg_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'neg_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences.du_equiv'45'iff''_66
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased erased)
-- foundation.negation.no-fixed-points-neg
d_no'45'fixed'45'points'45'neg_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_no'45'fixed'45'points'45'neg_64 = erased
-- foundation.negation.no-fixed-points-neg-Prop
d_no'45'fixed'45'points'45'neg'45'Prop_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_no'45'fixed'45'points'45'neg'45'Prop_80 = erased
