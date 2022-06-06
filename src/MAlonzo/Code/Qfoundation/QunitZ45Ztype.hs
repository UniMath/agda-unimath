{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QunitZ45Ztype where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels

-- foundation.unit-type.unit
d_unit_4 = ()
data T_unit_4 = C_star_6
-- foundation.unit-type.ind-unit
d_ind'45'unit_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (T_unit_4 -> ()) -> AgdaAny -> T_unit_4 -> AgdaAny
d_ind'45'unit_14 ~v0 ~v1 v2 ~v3 = du_ind'45'unit_14 v2
du_ind'45'unit_14 :: AgdaAny -> AgdaAny
du_ind'45'unit_14 v0 = coe v0
-- foundation.unit-type.terminal-map
d_terminal'45'map_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> T_unit_4
d_terminal'45'map_22 = erased
-- foundation.unit-type.raise-unit
d_raise'45'unit_28 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> ()
d_raise'45'unit_28 = erased
-- foundation.unit-type.raise-star
d_raise'45'star_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10
d_raise'45'star_34 ~v0 = du_raise'45'star_34
du_raise'45'star_34 ::
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10
du_raise'45'star_34
  = coe
      MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.C_map'45'raise_18
      erased
-- foundation.unit-type.equiv-raise-unit
d_equiv'45'raise'45'unit_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'raise'45'unit_38 ~v0 = du_equiv'45'raise'45'unit_38
du_equiv'45'raise'45'unit_38 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'raise'45'unit_38
  = coe
      MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50
-- foundation.unit-type.is-contr-unit
d_is'45'contr'45'unit_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'unit_42
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased erased
-- foundation.unit-type._.is-equiv-terminal-map-is-contr
d_is'45'equiv'45'terminal'45'map'45'is'45'contr_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'terminal'45'map'45'is'45'contr_52 ~v0 ~v1 v2
  = du_is'45'equiv'45'terminal'45'map'45'is'45'contr_52 v2
du_is'45'equiv'45'terminal'45'map'45'is'45'contr_52 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'terminal'45'map'45'is'45'contr_52 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (let v1
                = coe
                    MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
                    (coe v0) in
          coe (\ v2 -> v1))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
                 (coe v0)))
         erased)
-- foundation.unit-type._.is-contr-is-equiv-const
d_is'45'contr'45'is'45'equiv'45'const_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'const_64 ~v0 ~v1 v2
  = du_is'45'contr'45'is'45'equiv'45'const_64 v2
du_is'45'contr'45'is'45'equiv'45'const_64 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'const_64 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                seq (coe v1)
                (case coe v2 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v3 erased
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe
                seq (coe v1)
                (case coe v2 of
                   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
                     -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- foundation.unit-type.is-prop-unit
d_is'45'prop'45'unit_82 ::
  T_unit_4 ->
  T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'unit_82 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416
-- foundation.unit-type.unit-Prop
d_unit'45'Prop_84 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unit'45'Prop_84
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'prop'45'unit_82)
-- foundation.unit-type.is-set-unit
d_is'45'set'45'unit_86 ::
  T_unit_4 ->
  T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'unit_86
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.d_is'45'trunc'45'succ'45'is'45'trunc_48
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10
      () erased d_is'45'prop'45'unit_82
-- foundation.unit-type.unit-Set
d_unit'45'Set_88 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unit'45'Set_88
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'unit_86)
-- foundation.unit-type.is-contr-raise-unit
d_is'45'contr'45'raise'45'unit_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'raise'45'unit_92 ~v0
  = du_is'45'contr'45'raise'45'unit_92
du_is'45'contr'45'raise'45'unit_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'raise'45'unit_92
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)
      (coe d_is'45'contr'45'unit_42)
-- foundation.unit-type.is-prop-raise-unit
d_is'45'prop'45'raise'45'unit_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'raise'45'unit_98 ~v0
  = du_is'45'prop'45'raise'45'unit_98
du_is'45'prop'45'raise'45'unit_98 ::
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.T_raise_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'raise'45'unit_98
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'equiv''_222
      (coe
         MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)
      d_is'45'prop'45'unit_82
-- foundation.unit-type.raise-unit-Prop
d_raise'45'unit'45'Prop_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_raise'45'unit'45'Prop_104 ~v0 = du_raise'45'unit'45'Prop_104
du_raise'45'unit'45'Prop_104 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_raise'45'unit'45'Prop_104
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'raise'45'unit_98)
