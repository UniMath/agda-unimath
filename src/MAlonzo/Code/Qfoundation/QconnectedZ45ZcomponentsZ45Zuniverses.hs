{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QconnectedZ45ZcomponentsZ45Zuniverses where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple
import qualified MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequivalences
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels

-- foundation.connected-components-universes.component-UU-Level
d_component'45'UU'45'Level_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_component'45'UU'45'Level_10 = erased
-- foundation.connected-components-universes.type-component-UU-Level
d_type'45'component'45'UU'45'Level_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'component'45'UU'45'Level_22 = erased
-- foundation.connected-components-universes.mere-equiv-component-UU-Level
d_mere'45'equiv'45'component'45'UU'45'Level_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_mere'45'equiv'45'component'45'UU'45'Level_34 ~v0 ~v1 ~v2 v3
  = du_mere'45'equiv'45'component'45'UU'45'Level_34 v3
du_mere'45'equiv'45'component'45'UU'45'Level_34 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_mere'45'equiv'45'component'45'UU'45'Level_34 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe v0)
-- foundation.connected-components-universes.component-UU
d_component'45'UU_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_component'45'UU_42 = erased
-- foundation.connected-components-universes.type-component-UU
d_type'45'component'45'UU_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_type'45'component'45'UU_54 = erased
-- foundation.connected-components-universes.mere-equiv-component-UU
d_mere'45'equiv'45'component'45'UU_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_mere'45'equiv'45'component'45'UU_64 ~v0 ~v1 v2
  = du_mere'45'equiv'45'component'45'UU_64 v2
du_mere'45'equiv'45'component'45'UU_64 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_mere'45'equiv'45'component'45'UU_64 v0
  = coe du_mere'45'equiv'45'component'45'UU'45'Level_34 (coe v0)
-- foundation.connected-components-universes.equiv-component-UU-Level
d_equiv'45'component'45'UU'45'Level_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'component'45'UU'45'Level_78 = erased
-- foundation.connected-components-universes.id-equiv-component-UU-Level
d_id'45'equiv'45'component'45'UU'45'Level_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'component'45'UU'45'Level_92 ~v0 ~v1 ~v2 ~v3
  = du_id'45'equiv'45'component'45'UU'45'Level_92
du_id'45'equiv'45'component'45'UU'45'Level_92 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'component'45'UU'45'Level_92
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92
-- foundation.connected-components-universes.equiv-eq-component-UU-Level
d_equiv'45'eq'45'component'45'UU'45'Level_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'component'45'UU'45'Level_106 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5
  = du_equiv'45'eq'45'component'45'UU'45'Level_106
du_equiv'45'eq'45'component'45'UU'45'Level_106 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'component'45'UU'45'Level_106
  = coe du_id'45'equiv'45'component'45'UU'45'Level_92
-- foundation.connected-components-universes.is-contr-total-equiv-component-UU-Level
d_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118 ~v0
                                                                ~v1 ~v2 v3
  = du_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118
      v3
du_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QsubtypeZ45ZidentityZ45Zprinciple.du_is'45'contr'45'total'45'Eq'45'subtype_30
      (\ v1 ->
         coe
           MAlonzo.Code.Qfoundation.QmereZ45Zequivalences.du_is'45'prop'45'mere'45'equiv_32)
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
      (coe du_mere'45'equiv'45'component'45'UU'45'Level_34 (coe v0))
-- foundation.connected-components-universes.is-equiv-equiv-eq-component-UU-Level
d_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 ~v0
                                                             ~v1 ~v2 v3
  = du_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 v3
du_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe v0)
-- foundation.connected-components-universes.eq-equiv-component-UU-Level
d_eq'45'equiv'45'component'45'UU'45'Level_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'component'45'UU'45'Level_150 = erased
-- foundation.connected-components-universes.equiv-component-UU
d_equiv'45'component'45'UU_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'component'45'UU_164 = erased
-- foundation.connected-components-universes.id-equiv-component-UU
d_id'45'equiv'45'component'45'UU_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'component'45'UU_176 ~v0 ~v1 ~v2
  = du_id'45'equiv'45'component'45'UU_176
du_id'45'equiv'45'component'45'UU_176 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'component'45'UU_176
  = coe du_id'45'equiv'45'component'45'UU'45'Level_92
-- foundation.connected-components-universes.equiv-eq-component-UU
d_equiv'45'eq'45'component'45'UU_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'component'45'UU_188 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'eq'45'component'45'UU_188
du_equiv'45'eq'45'component'45'UU_188 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'component'45'UU_188
  = coe du_equiv'45'eq'45'component'45'UU'45'Level_106
-- foundation.connected-components-universes.is-contr-total-equiv-component-UU
d_is'45'contr'45'total'45'equiv'45'component'45'UU_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'equiv'45'component'45'UU_198 ~v0 ~v1 v2
  = du_is'45'contr'45'total'45'equiv'45'component'45'UU_198 v2
du_is'45'contr'45'total'45'equiv'45'component'45'UU_198 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'equiv'45'component'45'UU_198 v0
  = coe
      du_is'45'contr'45'total'45'equiv'45'component'45'UU'45'Level_118
      (coe v0)
-- foundation.connected-components-universes.is-equiv-equiv-eq-component-UU
d_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210 ~v0 ~v1 v2 v3
  = du_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210 v2 v3
du_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'equiv'45'eq'45'component'45'UU_210 v0 v1
  = coe
      du_is'45'equiv'45'equiv'45'eq'45'component'45'UU'45'Level_134 v0 v1
-- foundation.connected-components-universes.eq-equiv-component-UU
d_eq'45'equiv'45'component'45'UU_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'equiv'45'component'45'UU_224 = erased
-- foundation.connected-components-universes.is-contr-component-UU-Level-empty
d_is'45'contr'45'component'45'UU'45'Level'45'empty_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'component'45'UU'45'Level'45'empty_232 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased
         (coe
            MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
            v0
            (coe
               MAlonzo.Code.Qfoundation.QraisingZ45ZuniverseZ45Zlevels.du_equiv'45'raise_50)))
      erased
-- foundation.connected-components-universes.is-contr-component-UU-empty
d_is'45'contr'45'component'45'UU'45'empty_246 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'component'45'UU'45'empty_246
  = coe
      d_is'45'contr'45'component'45'UU'45'Level'45'empty_232
      (coe MAlonzo.Code.Agda.Primitive.d_lzero_16)
-- foundation.connected-components-universes.is-path-connected-component-UU
d_is'45'path'45'connected'45'component'45'UU_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'component'45'UU_252 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes.du_is'45'path'45'connected'45'mere'45'eq_54
      (coe ())
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v1)
         (coe
            MAlonzo.Code.Qfoundation.QmereZ45Zequivalences.du_refl'45'mere'45'equiv_42
            (coe v0)))
