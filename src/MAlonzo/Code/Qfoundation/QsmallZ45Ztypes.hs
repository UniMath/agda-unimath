{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QsmallZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Zpropositions
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype

-- foundation.small-types.is-small
d_is'45'small_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'small_10 = erased
-- foundation.small-types.type-is-small
d_type'45'is'45'small_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'is'45'small_24 = erased
-- foundation.small-types.equiv-is-small
d_equiv'45'is'45'small_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'is'45'small_34 ~v0 ~v1 ~v2 = du_equiv'45'is'45'small_34
du_equiv'45'is'45'small_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'is'45'small_34
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
-- foundation.small-types.map-equiv-is-small
d_map'45'equiv'45'is'45'small_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'is'45'small_44 ~v0 ~v1 ~v2 v3
  = du_map'45'equiv'45'is'45'small_44 v3
du_map'45'equiv'45'is'45'small_44 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'is'45'small_44 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe du_equiv'45'is'45'small_34 v0)
-- foundation.small-types.map-inv-equiv-is-small
d_map'45'inv'45'equiv'45'is'45'small_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'inv'45'equiv'45'is'45'small_56 ~v0 ~v1 ~v2 v3
  = du_map'45'inv'45'equiv'45'is'45'small_56 v3
du_map'45'inv'45'equiv'45'is'45'small_56 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'inv'45'equiv'45'is'45'small_56 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe du_equiv'45'is'45'small_34 v0)
-- foundation.small-types.UU-is-small
d_UU'45'is'45'small_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_UU'45'is'45'small_64 = erased
-- foundation.small-types.is-small-lsuc
d_is'45'small'45'lsuc_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'lsuc_74 ~v0 ~v1 = du_is'45'small'45'lsuc_74
du_is'45'small'45'lsuc_74 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'lsuc_74
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)
-- foundation.small-types.is-small-equiv
d_is'45'small'45'equiv_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'equiv_88 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_is'45'small'45'equiv_88 v5 v6
du_is'45'small'45'equiv_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'equiv_88 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe
                MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386 v3
                v0
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.small-types.is-small-equiv'
d_is'45'small'45'equiv''_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'equiv''_120 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'small'45'equiv''_120 v5
du_is'45'small'45'equiv''_120 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'equiv''_120 v0
  = coe
      du_is'45'small'45'equiv_88
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v0))
-- foundation.small-types.is-small-Σ
d_is'45'small'45'Σ_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'Σ_140 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_is'45'small'45'Σ_140 v5 v6
du_is'45'small'45'Σ_140 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'Σ_140 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> coe
                MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'Σ_544
                (coe v3)
                (coe
                   (\ v4 ->
                      coe
                        MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                        (coe
                           MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_equiv'45'tr_274)
                        (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                           (coe v1 v4))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.small-types.is-small-is-contr
d_is'45'small'45'is'45'contr_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'is'45'contr_176 ~v0 ~v1 ~v2 v3
  = du_is'45'small'45'is'45'contr_176 v3
du_is'45'small'45'is'45'contr_176 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'is'45'contr_176 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_equiv'45'is'45'contr_250
         (coe v0)
         (coe
            MAlonzo.Code.Qfoundation.QunitZ45Ztype.du_is'45'contr'45'raise'45'unit_92))
-- foundation.small-types.is-small-Π
d_is'45'small'45'Π_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'Π_200 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_is'45'small'45'Π_200 v0 v5 v6
du_is'45'small'45'Π_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'Π_200 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe seq (coe v1) (coe ()))
      (case coe v1 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
           -> coe
                MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_equiv'45'Π_262
                (coe v0) (coe v4)
                (coe
                   (\ v5 ->
                      coe
                        MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                        (coe
                           MAlonzo.Code.Qfoundation.QidentityZ45Ztypes.du_equiv'45'tr_274)
                        (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
                           (coe v2 v5))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.small-types.equiv-UU-is-small
d_equiv'45'UU'45'is'45'small_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'UU'45'is'45'small_234 ~v0 ~v1
  = du_equiv'45'UU'45'is'45'small_234
du_equiv'45'UU'45'is'45'small_234 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'UU'45'is'45'small_234
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
                 (coe
                    (\ v1 ->
                       coe
                         MAlonzo.Code.Qfoundation.Qequivalences.du_equiv'45'inv'45'equiv_858)))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'left'45'swap'45'Σ_464)
-- foundation.small-types.is-small-decidable-Prop
d_is'45'small'45'decidable'45'Prop_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'decidable'45'Prop_248 ~v0 ~v1
  = du_is'45'small'45'decidable'45'Prop_248
du_is'45'small'45'decidable'45'Prop_248 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'decidable'45'Prop_248
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
         (coe
            MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)
         (coe
            MAlonzo.Code.Qfoundation.QdecidableZ45Zpropositions.du_equiv'45'bool'45'decidable'45'Prop_88))
-- foundation.small-types.is-prop-is-small
d_is'45'prop'45'is'45'small_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'small_264 ~v0 ~v1 ~v2
  = du_is'45'prop'45'is'45'small_264
du_is'45'prop'45'is'45'small_264 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'small_264 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'is'45'proof'45'irrelevant_114
-- foundation.small-types.is-small-Prop
d_is'45'small'45'Prop_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'Prop_282 ~v0 ~v1 ~v2 = du_is'45'small'45'Prop_282
du_is'45'small'45'Prop_282 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'Prop_282
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'small_264)
-- foundation.small-types.is-small-mere-equiv
d_is'45'small'45'mere'45'equiv_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'small'45'mere'45'equiv_302 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_is'45'small'45'mere'45'equiv_302 v5 v6
du_is'45'small'45'mere'45'equiv_302 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'small'45'mere'45'equiv_302 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe ()) (coe v0) (coe du_is'45'small'45'Prop_282)
      (coe (\ v2 -> coe du_is'45'small'45'equiv_88 (coe v2) (coe v1)))
