import Omi.Wire

/-!
# Brasil, Bolsa, Balcão Binary Entry Point v7.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.B3B3derivativesBinaryentrypointSbeV70

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Simple OrdType: one byte code -/
def SimpleOrdtype.codes : List UInt8 :=
  [0x31, 0x32]

inductive SimpleOrdtype where
  | market -- Market
  | limit -- Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleOrdtype.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleOrdtype

def toByte : SimpleOrdtype → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleOrdtype :=
  if byte = 0x31 then .market
  else .limit

def ofByte (byte : UInt8) : SimpleOrdtype :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleOrdtype) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleOrdtype) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleOrdtype × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleOrdtype) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SimpleOrdtype) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleOrdtype

/-- Time In Force Simple: one byte code -/
def TimeInForceSimple.codes : List UInt8 :=
  [0x30, 0x33, 0x34]

inductive TimeInForceSimple where
  | day -- Day
  | immediateOrCancel -- Immediate Or Cancel
  | fillOrKill -- Fill Or Kill
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForceSimple.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForceSimple

def toByte : TimeInForceSimple → UInt8
  | .day => 0x30
  | .immediateOrCancel => 0x33
  | .fillOrKill => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForceSimple :=
  if byte = 0x30 then .day
  else if byte = 0x33 then .immediateOrCancel
  else .fillOrKill

def ofByte (byte : UInt8) : TimeInForceSimple :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForceSimple) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | immediateOrCancel => decide
  | fillOrKill => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForceSimple) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForceSimple × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForceSimple) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForceSimple) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForceSimple

/-- OrdType: one byte code -/
def Ordtype.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x4B, 0x57, 0x50]

inductive Ordtype where
  | market -- Market
  | limit -- Limit
  | stopLoss -- Stop Loss
  | stopLimit -- Stop Limit
  | marketWithLeftoverAsLimit -- Market With Leftover As Limit
  | rlp -- Rlp
  | peggedMidpoint -- Pegged Midpoint
  | unlisted (byte : { byte : UInt8 // byte ∉ Ordtype.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Ordtype

def toByte : Ordtype → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .stopLoss => 0x33
  | .stopLimit => 0x34
  | .marketWithLeftoverAsLimit => 0x4B
  | .rlp => 0x57
  | .peggedMidpoint => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Ordtype :=
  if byte = 0x31 then .market
  else if byte = 0x32 then .limit
  else if byte = 0x33 then .stopLoss
  else if byte = 0x34 then .stopLimit
  else if byte = 0x4B then .marketWithLeftoverAsLimit
  else if byte = 0x57 then .rlp
  else .peggedMidpoint

def ofByte (byte : UInt8) : Ordtype :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Ordtype) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | stopLoss => decide
  | stopLimit => decide
  | marketWithLeftoverAsLimit => decide
  | rlp => decide
  | peggedMidpoint => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Ordtype) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Ordtype × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Ordtype) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Ordtype) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Ordtype

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x34, 0x36, 0x37, 0x41]

inductive TimeInForce where
  | day -- Day
  | goodTillCancel -- Good Till Cancel
  | immediateOrCancel -- Immediate Or Cancel
  | fillOrKill -- Fill Or Kill
  | goodTillDate -- Good Till Date
  | atTheClose -- At The Close
  | goodForAuction -- Good For Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .goodTillCancel => 0x31
  | .immediateOrCancel => 0x33
  | .fillOrKill => 0x34
  | .goodTillDate => 0x36
  | .atTheClose => 0x37
  | .goodForAuction => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .goodTillCancel
  else if byte = 0x33 then .immediateOrCancel
  else if byte = 0x34 then .fillOrKill
  else if byte = 0x36 then .goodTillDate
  else if byte = 0x37 then .atTheClose
  else .goodForAuction

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | goodTillCancel => decide
  | immediateOrCancel => decide
  | fillOrKill => decide
  | goodTillDate => decide
  | atTheClose => decide
  | goodForAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Time In Force Optional: one byte code -/
def TimeInForceOptional.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x34, 0x36, 0x37, 0x41]

inductive TimeInForceOptional where
  | day -- Day
  | goodTillCancel -- Good Till Cancel
  | immediateOrCancel -- Immediate Or Cancel
  | fillOrKill -- Fill Or Kill
  | goodTillDate -- Good Till Date
  | atTheClose -- At The Close
  | goodForAuction -- Good For Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForceOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForceOptional

def toByte : TimeInForceOptional → UInt8
  | .day => 0x30
  | .goodTillCancel => 0x31
  | .immediateOrCancel => 0x33
  | .fillOrKill => 0x34
  | .goodTillDate => 0x36
  | .atTheClose => 0x37
  | .goodForAuction => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForceOptional :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .goodTillCancel
  else if byte = 0x33 then .immediateOrCancel
  else if byte = 0x34 then .fillOrKill
  else if byte = 0x36 then .goodTillDate
  else if byte = 0x37 then .atTheClose
  else .goodForAuction

def ofByte (byte : UInt8) : TimeInForceOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForceOptional) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | goodTillCancel => decide
  | immediateOrCancel => decide
  | fillOrKill => decide
  | goodTillDate => decide
  | atTheClose => decide
  | goodForAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForceOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForceOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForceOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForceOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForceOptional

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x35, 0x38, 0x43, 0x52, 0x5A]

inductive OrdStatus where
  | new -- New
  | partiallyFilled -- Partially Filled
  | filled -- Filled
  | canceled -- Canceled
  | replaced -- Replaced
  | rejected -- Rejected
  | expired -- Expired
  | restated -- Restated
  | previousFinalState -- Previous Final State
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partiallyFilled => 0x31
  | .filled => 0x32
  | .canceled => 0x34
  | .replaced => 0x35
  | .rejected => 0x38
  | .expired => 0x43
  | .restated => 0x52
  | .previousFinalState => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyFilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .canceled
  else if byte = 0x35 then .replaced
  else if byte = 0x38 then .rejected
  else if byte = 0x43 then .expired
  else if byte = 0x52 then .restated
  else .previousFinalState

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partiallyFilled => decide
  | filled => decide
  | canceled => decide
  | replaced => decide
  | rejected => decide
  | expired => decide
  | restated => decide
  | previousFinalState => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Multi Leg Reporting Type: one byte code -/
def MultiLegReportingType.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive MultiLegReportingType where
  | singleSecurity -- Single Security
  | individuallegOfMultilegSecurity -- Individualleg Of Multileg Security
  | multilegSecurity -- Multileg Security
  | unlisted (byte : { byte : UInt8 // byte ∉ MultiLegReportingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MultiLegReportingType

def toByte : MultiLegReportingType → UInt8
  | .singleSecurity => 0x31
  | .individuallegOfMultilegSecurity => 0x32
  | .multilegSecurity => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MultiLegReportingType :=
  if byte = 0x31 then .singleSecurity
  else if byte = 0x32 then .individuallegOfMultilegSecurity
  else .multilegSecurity

def ofByte (byte : UInt8) : MultiLegReportingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MultiLegReportingType) : ofByte value.toByte = value := by
  cases value with
  | singleSecurity => decide
  | individuallegOfMultilegSecurity => decide
  | multilegSecurity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MultiLegReportingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MultiLegReportingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MultiLegReportingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MultiLegReportingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MultiLegReportingType

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x46, 0x48]

inductive ExecType where
  | trade -- Trade
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .trade => 0x46
  | .tradeCancel => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x46 then .trade
  else .tradeCancel

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | trade => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Order Category: one byte code -/
def OrderCategory.codes : List UInt8 :=
  [0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48]

inductive OrderCategory where
  | resultOfOptionsExercise -- Result Of Options Exercise
  | resultOfAssignmentFromAnOptionsExercise -- Result Of Assignment From An Options Exercise
  | resultOfAutomaticOptionsExercise -- Result Of Automatic Options Exercise
  | resultOfMidpointOrder -- Result Of Midpoint Order
  | resultOfBlockBookTrade -- Result Of Block Book Trade
  | resultOfTradeAtClose -- Result Of Trade At Close
  | resultOfTradeAtAverage -- Result Of Trade At Average
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCategory

def toByte : OrderCategory → UInt8
  | .resultOfOptionsExercise => 0x42
  | .resultOfAssignmentFromAnOptionsExercise => 0x43
  | .resultOfAutomaticOptionsExercise => 0x44
  | .resultOfMidpointOrder => 0x45
  | .resultOfBlockBookTrade => 0x46
  | .resultOfTradeAtClose => 0x47
  | .resultOfTradeAtAverage => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCategory :=
  if byte = 0x42 then .resultOfOptionsExercise
  else if byte = 0x43 then .resultOfAssignmentFromAnOptionsExercise
  else if byte = 0x44 then .resultOfAutomaticOptionsExercise
  else if byte = 0x45 then .resultOfMidpointOrder
  else if byte = 0x46 then .resultOfBlockBookTrade
  else if byte = 0x47 then .resultOfTradeAtClose
  else .resultOfTradeAtAverage

def ofByte (byte : UInt8) : OrderCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCategory) : ofByte value.toByte = value := by
  cases value with
  | resultOfOptionsExercise => decide
  | resultOfAssignmentFromAnOptionsExercise => decide
  | resultOfAutomaticOptionsExercise => decide
  | resultOfMidpointOrder => decide
  | resultOfBlockBookTrade => decide
  | resultOfTradeAtClose => decide
  | resultOfTradeAtAverage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCategory

/-- Settl Type Optional: one byte code -/
def SettlTypeOptional.codes : List UInt8 :=
  [0x30, 0x38, 0x58]

inductive SettlTypeOptional where
  | buyersDiscretion -- Buyers Discretion
  | sellersDiscretion -- Sellers Discretion
  | mutual_ -- Mutual
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlTypeOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlTypeOptional

def toByte : SettlTypeOptional → UInt8
  | .buyersDiscretion => 0x30
  | .sellersDiscretion => 0x38
  | .mutual_ => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlTypeOptional :=
  if byte = 0x30 then .buyersDiscretion
  else if byte = 0x38 then .sellersDiscretion
  else .mutual_

def ofByte (byte : UInt8) : SettlTypeOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlTypeOptional) : ofByte value.toByte = value := by
  cases value with
  | buyersDiscretion => decide
  | sellersDiscretion => decide
  | mutual_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlTypeOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlTypeOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlTypeOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlTypeOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlTypeOptional

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x31, 0x32]

inductive LegSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- Settl Type: one byte code -/
def SettlType.codes : List UInt8 :=
  [0x30, 0x38, 0x58]

inductive SettlType where
  | buyersDiscretion -- Buyers Discretion
  | sellersDiscretion -- Sellers Discretion
  | mutual_ -- Mutual
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlType

def toByte : SettlType → UInt8
  | .buyersDiscretion => 0x30
  | .sellersDiscretion => 0x38
  | .mutual_ => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlType :=
  if byte = 0x30 then .buyersDiscretion
  else if byte = 0x38 then .sellersDiscretion
  else .mutual_

def ofByte (byte : UInt8) : SettlType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlType) : ofByte value.toByte = value := by
  cases value with
  | buyersDiscretion => decide
  | sellersDiscretion => decide
  | mutual_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlType

/-- Execute Underlying Trade: one byte code -/
def ExecuteUnderlyingTrade.codes : List UInt8 :=
  [0x30, 0x31]

inductive ExecuteUnderlyingTrade where
  | noUnderlyingTrade -- No Underlying Trade
  | underlyingOpposingTrade -- Underlying Opposing Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecuteUnderlyingTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecuteUnderlyingTrade

def toByte : ExecuteUnderlyingTrade → UInt8
  | .noUnderlyingTrade => 0x30
  | .underlyingOpposingTrade => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecuteUnderlyingTrade :=
  if byte = 0x30 then .noUnderlyingTrade
  else .underlyingOpposingTrade

def ofByte (byte : UInt8) : ExecuteUnderlyingTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecuteUnderlyingTrade) : ofByte value.toByte = value := by
  cases value with
  | noUnderlyingTrade => decide
  | underlyingOpposingTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecuteUnderlyingTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecuteUnderlyingTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecuteUnderlyingTrade) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecuteUnderlyingTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecuteUnderlyingTrade

/-- Quote Status Response To: one byte code -/
def QuoteStatusResponseTo.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive QuoteStatusResponseTo where
  | quote -- Quote
  | quoteRequest -- Quote Request
  | quoteCancel -- Quote Cancel
  | quoteRequestReject -- Quote Request Reject
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteStatusResponseTo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteStatusResponseTo

def toByte : QuoteStatusResponseTo → UInt8
  | .quote => 0x30
  | .quoteRequest => 0x31
  | .quoteCancel => 0x32
  | .quoteRequestReject => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteStatusResponseTo :=
  if byte = 0x30 then .quote
  else if byte = 0x31 then .quoteRequest
  else if byte = 0x32 then .quoteCancel
  else .quoteRequestReject

def ofByte (byte : UInt8) : QuoteStatusResponseTo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteStatusResponseTo) : ofByte value.toByte = value := by
  cases value with
  | quote => decide
  | quoteRequest => decide
  | quoteCancel => decide
  | quoteRequestReject => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteStatusResponseTo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteStatusResponseTo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteStatusResponseTo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteStatusResponseTo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteStatusResponseTo

/-- Side Optional: one byte code -/
def SideOptional.codes : List UInt8 :=
  [0x31, 0x32]

inductive SideOptional where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ SideOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideOptional

def toByte : SideOptional → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideOptional :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : SideOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideOptional) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideOptional

/-- Pos Maint Action: one byte code -/
def PosMaintAction.codes : List UInt8 :=
  [0x31, 0x33]

inductive PosMaintAction where
  | new -- New
  | cancel -- Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ PosMaintAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PosMaintAction

def toByte : PosMaintAction → UInt8
  | .new => 0x31
  | .cancel => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PosMaintAction :=
  if byte = 0x31 then .new
  else .cancel

def ofByte (byte : UInt8) : PosMaintAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PosMaintAction) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PosMaintAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PosMaintAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PosMaintAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PosMaintAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PosMaintAction

/-- Pos Maint Status: one byte code -/
def PosMaintStatus.codes : List UInt8 :=
  [0x30, 0x32, 0x33, 0x39]

inductive PosMaintStatus where
  | accepted -- Accepted
  | rejected -- Rejected
  | completed -- Completed
  | notExecuted -- Not Executed
  | unlisted (byte : { byte : UInt8 // byte ∉ PosMaintStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PosMaintStatus

def toByte : PosMaintStatus → UInt8
  | .accepted => 0x30
  | .rejected => 0x32
  | .completed => 0x33
  | .notExecuted => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PosMaintStatus :=
  if byte = 0x30 then .accepted
  else if byte = 0x32 then .rejected
  else if byte = 0x33 then .completed
  else .notExecuted

def ofByte (byte : UInt8) : PosMaintStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PosMaintStatus) : ofByte value.toByte = value := by
  cases value with
  | accepted => decide
  | rejected => decide
  | completed => decide
  | notExecuted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PosMaintStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PosMaintStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PosMaintStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PosMaintStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PosMaintStatus

/-- Pos Type: one byte code -/
def PosType.codes : List UInt8 :=
  [0x54, 0x53, 0x45, 0x42, 0x55, 0x43]

inductive PosType where
  | transactionQuantity -- Transaction Quantity
  | startOfDayQty -- Start Of Day Qty
  | optionExerciseQty -- Option Exercise Qty
  | blockedQty -- Blocked Qty
  | uncoveredQty -- Uncovered Qty
  | coveredQty -- Covered Qty
  | unlisted (byte : { byte : UInt8 // byte ∉ PosType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PosType

def toByte : PosType → UInt8
  | .transactionQuantity => 0x54
  | .startOfDayQty => 0x53
  | .optionExerciseQty => 0x45
  | .blockedQty => 0x42
  | .uncoveredQty => 0x55
  | .coveredQty => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PosType :=
  if byte = 0x54 then .transactionQuantity
  else if byte = 0x53 then .startOfDayQty
  else if byte = 0x45 then .optionExerciseQty
  else if byte = 0x42 then .blockedQty
  else if byte = 0x55 then .uncoveredQty
  else .coveredQty

def ofByte (byte : UInt8) : PosType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PosType) : ofByte value.toByte = value := by
  cases value with
  | transactionQuantity => decide
  | startOfDayQty => decide
  | optionExerciseQty => decide
  | blockedQty => decide
  | uncoveredQty => decide
  | coveredQty => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PosType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PosType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PosType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PosType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PosType

/-- Alloc Trans Type: one byte code -/
def AllocTransType.codes : List UInt8 :=
  [0x30, 0x32]

inductive AllocTransType where
  | new -- New
  | cancel -- Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocTransType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocTransType

def toByte : AllocTransType → UInt8
  | .new => 0x30
  | .cancel => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllocTransType :=
  if byte = 0x30 then .new
  else .cancel

def ofByte (byte : UInt8) : AllocTransType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocTransType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocTransType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocTransType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocTransType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocTransType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocTransType

/-- Alloc Type: one byte code -/
def AllocType.codes : List UInt8 :=
  [0x38]

inductive AllocType where
  | requestToIntermediary -- Request To Intermediary
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocType

def toByte : AllocType → UInt8
  | .requestToIntermediary => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AllocType :=
  .requestToIntermediary

def ofByte (byte : UInt8) : AllocType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocType) : ofByte value.toByte = value := by
  cases value with
  | requestToIntermediary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocType

/-- Alloc No Orders Type: one byte code -/
def AllocNoOrdersType.codes : List UInt8 :=
  [0x30]

inductive AllocNoOrdersType where
  | notSpecified -- Not Specified
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocNoOrdersType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocNoOrdersType

def toByte : AllocNoOrdersType → UInt8
  | .notSpecified => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AllocNoOrdersType :=
  .notSpecified

def ofByte (byte : UInt8) : AllocNoOrdersType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocNoOrdersType) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocNoOrdersType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocNoOrdersType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocNoOrdersType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocNoOrdersType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocNoOrdersType

/-- Alloc Report Type: one byte code -/
def AllocReportType.codes : List UInt8 :=
  [0x38]

inductive AllocReportType where
  | requestToIntermediary -- Request To Intermediary
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocReportType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocReportType

def toByte : AllocReportType → UInt8
  | .requestToIntermediary => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AllocReportType :=
  .requestToIntermediary

def ofByte (byte : UInt8) : AllocReportType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocReportType) : ofByte value.toByte = value := by
  cases value with
  | requestToIntermediary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocReportType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocReportType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocReportType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocReportType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocReportType

/-- Alloc Status: one byte code -/
def AllocStatus.codes : List UInt8 :=
  [0x30, 0x35]

inductive AllocStatus where
  | accepted -- Accepted
  | rejectedByIntermediary -- Rejected By Intermediary
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocStatus

def toByte : AllocStatus → UInt8
  | .accepted => 0x30
  | .rejectedByIntermediary => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllocStatus :=
  if byte = 0x30 then .accepted
  else .rejectedByIntermediary

def ofByte (byte : UInt8) : AllocStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocStatus) : ofByte value.toByte = value := by
  cases value with
  | accepted => decide
  | rejectedByIntermediary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocStatus

/-- Mass Action Response: one byte code -/
def MassActionResponse.codes : List UInt8 :=
  [0x30, 0x31]

inductive MassActionResponse where
  | rejected -- Rejected
  | accepted -- Accepted
  | unlisted (byte : { byte : UInt8 // byte ∉ MassActionResponse.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassActionResponse

def toByte : MassActionResponse → UInt8
  | .rejected => 0x30
  | .accepted => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassActionResponse :=
  if byte = 0x30 then .rejected
  else .accepted

def ofByte (byte : UInt8) : MassActionResponse :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassActionResponse) : ofByte value.toByte = value := by
  cases value with
  | rejected => decide
  | accepted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassActionResponse) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassActionResponse × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassActionResponse) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MassActionResponse) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassActionResponse

/-- Credentials -/
structure Credentials where
  credentialsData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Credentials

def encode (message : Credentials) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.credentialsData.val.length)
    ++ (encodeMany Byte.encode message.credentialsData.val)

def decode (bytes : List UInt8) : Option (Credentials × List UInt8) := do
  let (credentialsLength, bytes) ← decodeUInt 1 bytes
  let (credentialsData_, bytes) ← decodeMany Byte.decode credentialsLength.toNat bytes
  if fits_credentialsData : credentialsData_.length < 256 ^ 1 then
    pure ({ credentialsData := ⟨credentialsData_, fits_credentialsData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Credentials) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Credentials) : (encode message).length ≤ 256 := by
  have bound_credentialsData := message.credentialsData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Credentials) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.credentialsData.length_lt]
  rfl

end Credentials

/-- Client Ip -/
structure ClientIp where
  clientIpData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace ClientIp

def encode (message : ClientIp) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.clientIpData.val.length)
    ++ (encodeMany Byte.encode message.clientIpData.val)

def decode (bytes : List UInt8) : Option (ClientIp × List UInt8) := do
  let (clientIpLength, bytes) ← decodeUInt 1 bytes
  let (clientIpData_, bytes) ← decodeMany Byte.decode clientIpLength.toNat bytes
  if fits_clientIpData : clientIpData_.length < 256 ^ 1 then
    pure ({ clientIpData := ⟨clientIpData_, fits_clientIpData⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClientIp) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientIp) : (encode message).length ≤ 256 := by
  have bound_clientIpData := message.clientIpData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : ClientIp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.clientIpData.length_lt]
  rfl

end ClientIp

/-- Client App Name -/
structure ClientAppName where
  clientAppNameData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace ClientAppName

def encode (message : ClientAppName) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.clientAppNameData.val.length)
    ++ (encodeMany Byte.encode message.clientAppNameData.val)

def decode (bytes : List UInt8) : Option (ClientAppName × List UInt8) := do
  let (clientAppNameLength, bytes) ← decodeUInt 1 bytes
  let (clientAppNameData_, bytes) ← decodeMany Byte.decode clientAppNameLength.toNat bytes
  if fits_clientAppNameData : clientAppNameData_.length < 256 ^ 1 then
    pure ({ clientAppNameData := ⟨clientAppNameData_, fits_clientAppNameData⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClientAppName) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientAppName) : (encode message).length ≤ 256 := by
  have bound_clientAppNameData := message.clientAppNameData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : ClientAppName) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.clientAppNameData.length_lt]
  rfl

end ClientAppName

/-- Client App Version -/
structure ClientAppVersion where
  clientAppVersionData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace ClientAppVersion

def encode (message : ClientAppVersion) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.clientAppVersionData.val.length)
    ++ (encodeMany Byte.encode message.clientAppVersionData.val)

def decode (bytes : List UInt8) : Option (ClientAppVersion × List UInt8) := do
  let (clientAppVersionLength, bytes) ← decodeUInt 1 bytes
  let (clientAppVersionData_, bytes) ← decodeMany Byte.decode clientAppVersionLength.toNat bytes
  if fits_clientAppVersionData : clientAppVersionData_.length < 256 ^ 1 then
    pure ({ clientAppVersionData := ⟨clientAppVersionData_, fits_clientAppVersionData⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClientAppVersion) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientAppVersion) : (encode message).length ≤ 256 := by
  have bound_clientAppVersionData := message.clientAppVersionData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : ClientAppVersion) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.clientAppVersionData.length_lt]
  rfl

end ClientAppVersion

/-- Negotiate Message -/
structure NegotiateMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  timestamp : BitVec 64
  enteringFirm : BitVec 32
  onbehalfFirm : BitVec 32
  credentials : Credentials
  clientIp : ClientIp
  clientAppName : ClientAppName
  clientAppVersion : ClientAppVersion
  deriving DecidableEq, Repr

namespace NegotiateMessage

def encode (message : NegotiateMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.enteringFirm
    ++ (encodeUIntLE 4 message.onbehalfFirm
    ++ (Credentials.encode message.credentials
    ++ (ClientIp.encode message.clientIp
    ++ (ClientAppName.encode message.clientAppName
    ++ (ClientAppVersion.encode message.clientAppVersion))))))))

def decode (bytes : List UInt8) : Option (NegotiateMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (enteringFirm, bytes) ← decodeUIntLE 4 bytes
  let (onbehalfFirm, bytes) ← decodeUIntLE 4 bytes
  let (credentials, bytes) ← Credentials.decode bytes
  let (clientIp, bytes) ← ClientIp.decode bytes
  let (clientAppName, bytes) ← ClientAppName.decode bytes
  let (clientAppVersion, bytes) ← ClientAppVersion.decode bytes
  pure ({ sessionId, sessionVerId, timestamp, enteringFirm, onbehalfFirm, credentials, clientIp, clientAppName, clientAppVersion }, bytes)

theorem encode_length_pos (message : NegotiateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NegotiateMessage) : (encode message).length ≤ 1052 := by
  have bound_credentials := Credentials.encode_length_le message.credentials
  have bound_clientIp := ClientIp.encode_length_le message.clientIp
  have bound_clientAppName := ClientAppName.encode_length_le message.clientAppName
  have bound_clientAppVersion := ClientAppVersion.encode_length_le message.clientAppVersion
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : NegotiateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Credentials.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClientIp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClientAppName.decode_encode, some_bind]
  dsimp only
  rw [ClientAppVersion.decode_encode, some_bind]
  rfl

end NegotiateMessage

/-- Negotiate Response Message: 24 bytes -/
structure NegotiateResponseMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  requestTimestamp : BitVec 64
  enteringFirm : BitVec 32
  deriving DecidableEq, Repr

namespace NegotiateResponseMessage

def encode (message : NegotiateResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 4 message.enteringFirm)))

def decode (bytes : List UInt8) : Option (NegotiateResponseMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (enteringFirm, bytes) ← decodeUIntLE 4 bytes
  pure ({ sessionId, sessionVerId, requestTimestamp, enteringFirm }, bytes)

@[simp] theorem encode_length (message : NegotiateResponseMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NegotiateResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiateResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NegotiateResponseMessage

/-- Negotiate Reject Message: 36 bytes -/
structure NegotiateRejectMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  requestTimestamp : BitVec 64
  enteringFirmOptional : BitVec 32
  negotiationRejectCode : BitVec 8
  offset25Padding3 : Alpha 3
  currentSessionVerId : BitVec 64
  deriving DecidableEq, Repr

namespace NegotiateRejectMessage

def encode (message : NegotiateRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 4 message.enteringFirmOptional
    ++ (encodeUInt 1 message.negotiationRejectCode
    ++ (Alpha.encode message.offset25Padding3
    ++ (encodeUIntLE 8 message.currentSessionVerId))))))

def decode (bytes : List UInt8) : Option (NegotiateRejectMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (enteringFirmOptional, bytes) ← decodeUIntLE 4 bytes
  let (negotiationRejectCode, bytes) ← decodeUInt 1 bytes
  let (offset25Padding3, bytes) ← Alpha.decode 3 bytes
  let (currentSessionVerId, bytes) ← decodeUIntLE 8 bytes
  pure ({ sessionId, sessionVerId, requestTimestamp, enteringFirmOptional, negotiationRejectCode, offset25Padding3, currentSessionVerId }, bytes)

@[simp] theorem encode_length (message : NegotiateRejectMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NegotiateRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiateRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NegotiateRejectMessage

/-- Establish Message -/
structure EstablishMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  timestamp : BitVec 64
  keepAliveInterval : BitVec 64
  nextSeqNo : BitVec 32
  cancelOnDisconnectType : BitVec 8
  offset33Padding1 : Alpha 1
  codTimeoutWindow : BitVec 64
  credentials : Credentials
  deriving DecidableEq, Repr

namespace EstablishMessage

def encode (message : EstablishMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.keepAliveInterval
    ++ (encodeUIntLE 4 message.nextSeqNo
    ++ (encodeUInt 1 message.cancelOnDisconnectType
    ++ (Alpha.encode message.offset33Padding1
    ++ (encodeUIntLE 8 message.codTimeoutWindow
    ++ (Credentials.encode message.credentials))))))))

def decode (bytes : List UInt8) : Option (EstablishMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (keepAliveInterval, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (cancelOnDisconnectType, bytes) ← decodeUInt 1 bytes
  let (offset33Padding1, bytes) ← Alpha.decode 1 bytes
  let (codTimeoutWindow, bytes) ← decodeUIntLE 8 bytes
  let (credentials, bytes) ← Credentials.decode bytes
  pure ({ sessionId, sessionVerId, timestamp, keepAliveInterval, nextSeqNo, cancelOnDisconnectType, offset33Padding1, codTimeoutWindow, credentials }, bytes)

theorem encode_length_pos (message : EstablishMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EstablishMessage) : (encode message).length ≤ 298 := by
  have bound_credentials := Credentials.encode_length_le message.credentials
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : EstablishMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Credentials.decode_encode, some_bind]
  rfl

end EstablishMessage

/-- Establish Ack Message: 36 bytes -/
structure EstablishAckMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  requestTimestamp : BitVec 64
  keepAliveInterval : BitVec 64
  nextSeqNo : BitVec 32
  lastIncomingSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace EstablishAckMessage

def encode (message : EstablishAckMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 8 message.keepAliveInterval
    ++ (encodeUIntLE 4 message.nextSeqNo
    ++ (encodeUIntLE 4 message.lastIncomingSeqNo)))))

def decode (bytes : List UInt8) : Option (EstablishAckMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (keepAliveInterval, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (lastIncomingSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ sessionId, sessionVerId, requestTimestamp, keepAliveInterval, nextSeqNo, lastIncomingSeqNo }, bytes)

@[simp] theorem encode_length (message : EstablishAckMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EstablishAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EstablishAckMessage

/-- Establish Reject Message: 26 bytes -/
structure EstablishRejectMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  requestTimestamp : BitVec 64
  establishmentRejectCode : BitVec 8
  offset21Padding1 : Alpha 1
  lastIncomingSeqNoOptional : BitVec 32
  deriving DecidableEq, Repr

namespace EstablishRejectMessage

def encode (message : EstablishRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.establishmentRejectCode
    ++ (Alpha.encode message.offset21Padding1
    ++ (encodeUIntLE 4 message.lastIncomingSeqNoOptional)))))

def decode (bytes : List UInt8) : Option (EstablishRejectMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (establishmentRejectCode, bytes) ← decodeUInt 1 bytes
  let (offset21Padding1, bytes) ← Alpha.decode 1 bytes
  let (lastIncomingSeqNoOptional, bytes) ← decodeUIntLE 4 bytes
  pure ({ sessionId, sessionVerId, requestTimestamp, establishmentRejectCode, offset21Padding1, lastIncomingSeqNoOptional }, bytes)

@[simp] theorem encode_length (message : EstablishRejectMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : EstablishRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EstablishRejectMessage

/-- Terminate Message: 13 bytes -/
structure TerminateMessage where
  sessionId : BitVec 32
  sessionVerId : BitVec 64
  terminationCode : BitVec 8
  deriving DecidableEq, Repr

namespace TerminateMessage

def encode (message : TerminateMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.sessionVerId
    ++ (encodeUInt 1 message.terminationCode))

def decode (bytes : List UInt8) : Option (TerminateMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionVerId, bytes) ← decodeUIntLE 8 bytes
  let (terminationCode, bytes) ← decodeUInt 1 bytes
  pure ({ sessionId, sessionVerId, terminationCode }, bytes)

@[simp] theorem encode_length (message : TerminateMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TerminateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TerminateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TerminateMessage

/-- Not Applied Message: 8 bytes -/
structure NotAppliedMessage where
  fromSeqNo : BitVec 32
  count : BitVec 32
  deriving DecidableEq, Repr

namespace NotAppliedMessage

def encode (message : NotAppliedMessage) : List UInt8 :=
  encodeUIntLE 4 message.fromSeqNo
    ++ (encodeUIntLE 4 message.count)

def decode (bytes : List UInt8) : Option (NotAppliedMessage × List UInt8) := do
  let (fromSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  pure ({ fromSeqNo, count }, bytes)

@[simp] theorem encode_length (message : NotAppliedMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NotAppliedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotAppliedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NotAppliedMessage

/-- Sequence Message: 4 bytes -/
structure SequenceMessage where
  nextSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceMessage

def encode (message : SequenceMessage) : List UInt8 :=
  encodeUIntLE 4 message.nextSeqNo

def decode (bytes : List UInt8) : Option (SequenceMessage × List UInt8) := do
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ nextSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceMessage

/-- Retransmit Request Message: 20 bytes -/
structure RetransmitRequestMessage where
  sessionId : BitVec 32
  timestamp : BitVec 64
  fromSeqNo : BitVec 32
  count : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmitRequestMessage

def encode (message : RetransmitRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.fromSeqNo
    ++ (encodeUIntLE 4 message.count)))

def decode (bytes : List UInt8) : Option (RetransmitRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (fromSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  pure ({ sessionId, timestamp, fromSeqNo, count }, bytes)

@[simp] theorem encode_length (message : RetransmitRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmitRequestMessage

/-- Retransmission Message: 20 bytes -/
structure RetransmissionMessage where
  sessionId : BitVec 32
  requestTimestamp : BitVec 64
  nextSeqNo : BitVec 32
  count : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionMessage

def encode (message : RetransmissionMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 4 message.nextSeqNo
    ++ (encodeUIntLE 4 message.count)))

def decode (bytes : List UInt8) : Option (RetransmissionMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  pure ({ sessionId, requestTimestamp, nextSeqNo, count }, bytes)

@[simp] theorem encode_length (message : RetransmissionMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionMessage

/-- Retransmit Reject Message: 13 bytes -/
structure RetransmitRejectMessage where
  sessionId : BitVec 32
  requestTimestamp : BitVec 64
  retransmitRejectCode : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitRejectMessage

def encode (message : RetransmitRejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.retransmitRejectCode))

def decode (bytes : List UInt8) : Option (RetransmitRejectMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (retransmitRejectCode, bytes) ← decodeUInt 1 bytes
  pure ({ sessionId, requestTimestamp, retransmitRejectCode }, bytes)

@[simp] theorem encode_length (message : RetransmitRejectMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmitRejectMessage

/-- Inbound Business Header: 18 bytes -/
structure InboundBusinessHeader where
  sessionId : BitVec 32
  msgSeqNum : BitVec 32
  sendingTime : BitVec 64
  marketSegmentId : BitVec 8
  padding : Alpha 1
  deriving DecidableEq, Repr

namespace InboundBusinessHeader

def encode (message : InboundBusinessHeader) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUInt 1 message.marketSegmentId
    ++ (Alpha.encode message.padding))))

def decode (bytes : List UInt8) : Option (InboundBusinessHeader × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (padding, bytes) ← Alpha.decode 1 bytes
  pure ({ sessionId, msgSeqNum, sendingTime, marketSegmentId, padding }, bytes)

@[simp] theorem encode_length (message : InboundBusinessHeader) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InboundBusinessHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InboundBusinessHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InboundBusinessHeader

/-- Investor Id -/
structure InvestorId where
  investorIdData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace InvestorId

def encode (message : InvestorId) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.investorIdData.val.length)
    ++ (encodeMany Byte.encode message.investorIdData.val)

def decode (bytes : List UInt8) : Option (InvestorId × List UInt8) := do
  let (investorIdLength, bytes) ← decodeUInt 1 bytes
  let (investorIdData_, bytes) ← decodeMany Byte.decode investorIdLength.toNat bytes
  if fits_investorIdData : investorIdData_.length < 256 ^ 1 then
    pure ({ investorIdData := ⟨investorIdData_, fits_investorIdData⟩ }, bytes)
  else none

theorem encode_length_pos (message : InvestorId) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InvestorId) : (encode message).length ≤ 256 := by
  have bound_investorIdData := message.investorIdData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : InvestorId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.investorIdData.length_lt]
  rfl

end InvestorId

/-- Memo -/
structure Memo where
  memoData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Memo

def encode (message : Memo) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.memoData.val.length)
    ++ (encodeMany Byte.encode message.memoData.val)

def decode (bytes : List UInt8) : Option (Memo × List UInt8) := do
  let (memoLength, bytes) ← decodeUInt 1 bytes
  let (memoData_, bytes) ← decodeMany Byte.decode memoLength.toNat bytes
  if fits_memoData : memoData_.length < 256 ^ 1 then
    pure ({ memoData := ⟨memoData_, fits_memoData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Memo) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Memo) : (encode message).length ≤ 256 := by
  have bound_memoData := message.memoData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Memo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.memoData.length_lt]
  rfl

end Memo

/-- Simple New Order Message -/
structure SimpleNewOrderMessage where
  inboundBusinessHeader : InboundBusinessHeader
  ordtagid : BitVec 8
  mmProtectionReset : BitVec 8
  clordid : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  selfTradePreventionInstruction : BitVec 8
  securityId : BitVec 64
  side : Side
  simpleOrdtype : SimpleOrdtype
  timeInForceSimple : TimeInForceSimple
  offset59Padding1 : Alpha 1
  orderQty : BitVec 64
  priceOptional : BitVec 64
  investorId : InvestorId
  memo : Memo
  deriving DecidableEq, Repr

namespace SimpleNewOrderMessage

def encode (message : SimpleNewOrderMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUInt 1 message.ordtagid
    ++ (encodeUInt 1 message.mmProtectionReset
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUInt 1 message.selfTradePreventionInstruction
    ++ (encodeUIntLE 8 message.securityId
    ++ (Side.encode message.side
    ++ (SimpleOrdtype.encode message.simpleOrdtype
    ++ (TimeInForceSimple.encode message.timeInForceSimple
    ++ (Alpha.encode message.offset59Padding1
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (InvestorId.encode message.investorId
    ++ (Memo.encode message.memo))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleNewOrderMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (selfTradePreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (simpleOrdtype, bytes) ← SimpleOrdtype.decode bytes
  let (timeInForceSimple, bytes) ← TimeInForceSimple.decode bytes
  let (offset59Padding1, bytes) ← Alpha.decode 1 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (investorId, bytes) ← InvestorId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, ordtagid, mmProtectionReset, clordid, account, senderLocation, enteringTrader, selfTradePreventionInstruction, securityId, side, simpleOrdtype, timeInForceSimple, offset59Padding1, orderQty, priceOptional, investorId, memo }, bytes)

theorem encode_length_pos (message : SimpleNewOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleNewOrderMessage) : (encode message).length ≤ 588 := by
  have bound_investorId := InvestorId.encode_length_le message.investorId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, SimpleOrdtype.encode_length, TimeInForceSimple.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleNewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleOrdtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForceSimple.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end SimpleNewOrderMessage

/-- Simple Modify Order Message -/
structure SimpleModifyOrderMessage where
  inboundBusinessHeader : InboundBusinessHeader
  ordtagid : BitVec 8
  mmProtectionReset : BitVec 8
  clordid : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  selfTradePreventionInstruction : BitVec 8
  securityId : BitVec 64
  side : Side
  simpleOrdtype : SimpleOrdtype
  timeInForceSimple : TimeInForceSimple
  offset59Padding1 : Alpha 1
  orderQty : BitVec 64
  priceOptional : BitVec 64
  orderIdOptional : BitVec 64
  origclordid : BitVec 64
  investorId : InvestorId
  memo : Memo
  deriving DecidableEq, Repr

namespace SimpleModifyOrderMessage

def encode (message : SimpleModifyOrderMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUInt 1 message.ordtagid
    ++ (encodeUInt 1 message.mmProtectionReset
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUInt 1 message.selfTradePreventionInstruction
    ++ (encodeUIntLE 8 message.securityId
    ++ (Side.encode message.side
    ++ (SimpleOrdtype.encode message.simpleOrdtype
    ++ (TimeInForceSimple.encode message.timeInForceSimple
    ++ (Alpha.encode message.offset59Padding1
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origclordid
    ++ (InvestorId.encode message.investorId
    ++ (Memo.encode message.memo))))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleModifyOrderMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (selfTradePreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (simpleOrdtype, bytes) ← SimpleOrdtype.decode bytes
  let (timeInForceSimple, bytes) ← TimeInForceSimple.decode bytes
  let (offset59Padding1, bytes) ← Alpha.decode 1 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (investorId, bytes) ← InvestorId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, ordtagid, mmProtectionReset, clordid, account, senderLocation, enteringTrader, selfTradePreventionInstruction, securityId, side, simpleOrdtype, timeInForceSimple, offset59Padding1, orderQty, priceOptional, orderIdOptional, origclordid, investorId, memo }, bytes)

theorem encode_length_pos (message : SimpleModifyOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleModifyOrderMessage) : (encode message).length ≤ 604 := by
  have bound_investorId := InvestorId.encode_length_le message.investorId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, SimpleOrdtype.encode_length, TimeInForceSimple.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleModifyOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleOrdtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForceSimple.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end SimpleModifyOrderMessage

/-- Custodian Info: 12 bytes -/
structure CustodianInfo where
  custodian : BitVec 32
  custodyAccount : BitVec 32
  custodyAllocationType : BitVec 32
  deriving DecidableEq, Repr

namespace CustodianInfo

def encode (message : CustodianInfo) : List UInt8 :=
  encodeUIntLE 4 message.custodian
    ++ (encodeUIntLE 4 message.custodyAccount
    ++ (encodeUIntLE 4 message.custodyAllocationType))

def decode (bytes : List UInt8) : Option (CustodianInfo × List UInt8) := do
  let (custodian, bytes) ← decodeUIntLE 4 bytes
  let (custodyAccount, bytes) ← decodeUIntLE 4 bytes
  let (custodyAllocationType, bytes) ← decodeUIntLE 4 bytes
  pure ({ custodian, custodyAccount, custodyAllocationType }, bytes)

@[simp] theorem encode_length (message : CustodianInfo) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CustodianInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustodianInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CustodianInfo

/-- Desk Id -/
structure DeskId where
  deskIdData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace DeskId

def encode (message : DeskId) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.deskIdData.val.length)
    ++ (encodeMany Byte.encode message.deskIdData.val)

def decode (bytes : List UInt8) : Option (DeskId × List UInt8) := do
  let (deskIdLength, bytes) ← decodeUInt 1 bytes
  let (deskIdData_, bytes) ← decodeMany Byte.decode deskIdLength.toNat bytes
  if fits_deskIdData : deskIdData_.length < 256 ^ 1 then
    pure ({ deskIdData := ⟨deskIdData_, fits_deskIdData⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeskId) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeskId) : (encode message).length ≤ 256 := by
  have bound_deskIdData := message.deskIdData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : DeskId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.deskIdData.length_lt]
  rfl

end DeskId

/-- New Order Single Message -/
structure NewOrderSingleMessage where
  inboundBusinessHeader : InboundBusinessHeader
  ordtagid : BitVec 8
  mmProtectionReset : BitVec 8
  clordid : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  selfTradePreventionInstruction : BitVec 8
  securityId : BitVec 64
  side : Side
  ordtype : Ordtype
  timeInForce : TimeInForce
  offset59Padding1 : Alpha 1
  orderQty : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  executingTraderOptional : Alpha 5
  routingInstruction : BitVec 8
  expireDate : BitVec 16
  custodianInfo : CustodianInfo
  investorId : InvestorId
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace NewOrderSingleMessage

def encode (message : NewOrderSingleMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUInt 1 message.ordtagid
    ++ (encodeUInt 1 message.mmProtectionReset
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUInt 1 message.selfTradePreventionInstruction
    ++ (encodeUIntLE 8 message.securityId
    ++ (Side.encode message.side
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForce.encode message.timeInForce
    ++ (Alpha.encode message.offset59Padding1
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (Alpha.encode message.executingTraderOptional
    ++ (encodeUInt 1 message.routingInstruction
    ++ (encodeUIntLE 2 message.expireDate
    ++ (CustodianInfo.encode message.custodianInfo
    ++ (InvestorId.encode message.investorId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (selfTradePreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (offset59Padding1, bytes) ← Alpha.decode 1 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (executingTraderOptional, bytes) ← Alpha.decode 5 bytes
  let (routingInstruction, bytes) ← decodeUInt 1 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (custodianInfo, bytes) ← CustodianInfo.decode bytes
  let (investorId, bytes) ← InvestorId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, ordtagid, mmProtectionReset, clordid, account, senderLocation, enteringTrader, selfTradePreventionInstruction, securityId, side, ordtype, timeInForce, offset59Padding1, orderQty, priceOptional, stopPx, minQty, maxFloor, executingTraderOptional, routingInstruction, expireDate, custodianInfo, investorId, deskId, memo }, bytes)

theorem encode_length_pos (message : NewOrderSingleMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderSingleMessage) : (encode message).length ≤ 888 := by
  have bound_investorId := InvestorId.encode_length_le message.investorId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, Ordtype.encode_length, TimeInForce.encode_length, CustodianInfo.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CustodianInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end NewOrderSingleMessage

/-- Order Cancel Replace Request Message -/
structure OrderCancelReplaceRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  ordtagid : BitVec 8
  mmProtectionReset : BitVec 8
  clordid : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  selfTradePreventionInstruction : BitVec 8
  securityId : BitVec 64
  side : Side
  ordtype : Ordtype
  timeInForceOptional : TimeInForceOptional
  accountType : BitVec 8
  orderQty : BitVec 64
  priceOptional : BitVec 64
  orderIdOptional : BitVec 64
  origclordid : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  executingTraderOptional : Alpha 5
  routingInstruction : BitVec 8
  expireDate : BitVec 16
  custodianInfo : CustodianInfo
  investorId : InvestorId
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace OrderCancelReplaceRequestMessage

def encode (message : OrderCancelReplaceRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUInt 1 message.ordtagid
    ++ (encodeUInt 1 message.mmProtectionReset
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUInt 1 message.selfTradePreventionInstruction
    ++ (encodeUIntLE 8 message.securityId
    ++ (Side.encode message.side
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForceOptional.encode message.timeInForceOptional
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origclordid
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (Alpha.encode message.executingTraderOptional
    ++ (encodeUInt 1 message.routingInstruction
    ++ (encodeUIntLE 2 message.expireDate
    ++ (CustodianInfo.encode message.custodianInfo
    ++ (InvestorId.encode message.investorId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelReplaceRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (selfTradePreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForceOptional, bytes) ← TimeInForceOptional.decode bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (executingTraderOptional, bytes) ← Alpha.decode 5 bytes
  let (routingInstruction, bytes) ← decodeUInt 1 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (custodianInfo, bytes) ← CustodianInfo.decode bytes
  let (investorId, bytes) ← InvestorId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, ordtagid, mmProtectionReset, clordid, account, senderLocation, enteringTrader, selfTradePreventionInstruction, securityId, side, ordtype, timeInForceOptional, accountType, orderQty, priceOptional, orderIdOptional, origclordid, stopPx, minQty, maxFloor, executingTraderOptional, routingInstruction, expireDate, custodianInfo, investorId, deskId, memo }, bytes)

theorem encode_length_pos (message : OrderCancelReplaceRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderCancelReplaceRequestMessage) : (encode message).length ≤ 904 := by
  have bound_investorId := InvestorId.encode_length_le message.investorId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, Ordtype.encode_length, TimeInForceOptional.encode_length, CustodianInfo.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelReplaceRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForceOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CustodianInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end OrderCancelReplaceRequestMessage

/-- Order Cancel Request Message -/
structure OrderCancelRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  offset18Padding2 : Alpha 2
  clordid : BitVec 64
  securityId : BitVec 64
  orderIdOptional : BitVec 64
  origclordid : BitVec 64
  side : Side
  singleCancelRestatementReason : BitVec 8
  offset54Padding2 : Alpha 2
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTraderOptional : Alpha 5
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (Alpha.encode message.offset18Padding2
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origclordid
    ++ (Side.encode message.side
    ++ (encodeUInt 1 message.singleCancelRestatementReason
    ++ (Alpha.encode message.offset54Padding2
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTraderOptional
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (offset18Padding2, bytes) ← Alpha.decode 2 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (singleCancelRestatementReason, bytes) ← decodeUInt 1 bytes
  let (offset54Padding2, bytes) ← Alpha.decode 2 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTraderOptional, bytes) ← Alpha.decode 5 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, offset18Padding2, clordid, securityId, orderIdOptional, origclordid, side, singleCancelRestatementReason, offset54Padding2, senderLocation, enteringTrader, executingTraderOptional, deskId, memo }, bytes)

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderCancelRequestMessage) : (encode message).length ≤ 588 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, Alpha.encode_length, encodeUIntLE_length, Side.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end OrderCancelRequestMessage

/-- Cross Sides Group: 18 bytes -/
structure CrossSidesGroup where
  side : Side
  offset1Padding1 : Alpha 1
  account : BitVec 32
  enteringFirmOptional : BitVec 32
  clordid : BitVec 64
  deriving DecidableEq, Repr

namespace CrossSidesGroup

def encode (message : CrossSidesGroup) : List UInt8 :=
  Side.encode message.side
    ++ (Alpha.encode message.offset1Padding1
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 4 message.enteringFirmOptional
    ++ (encodeUIntLE 8 message.clordid))))

def decode (bytes : List UInt8) : Option (CrossSidesGroup × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (offset1Padding1, bytes) ← Alpha.decode 1 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (enteringFirmOptional, bytes) ← decodeUIntLE 4 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, offset1Padding1, account, enteringFirmOptional, clordid }, bytes)

@[simp] theorem encode_length (message : CrossSidesGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Side.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CrossSidesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossSidesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CrossSidesGroup

/-- Cross Sides Groups -/
structure CrossSidesGroups where
  blockLength : BitVec 16
  crossSidesGroup : Bounded 1 CrossSidesGroup
  deriving DecidableEq, Repr

namespace CrossSidesGroups

def encode (message : CrossSidesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.crossSidesGroup.val.length)
    ++ (encodeMany CrossSidesGroup.encode message.crossSidesGroup.val))

def decode (bytes : List UInt8) : Option (CrossSidesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (crossSidesGroup_, bytes) ← decodeMany CrossSidesGroup.decode numInGroup.toNat bytes
  if fits_crossSidesGroup : crossSidesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, crossSidesGroup := ⟨crossSidesGroup_, fits_crossSidesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CrossSidesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CrossSidesGroups) : (encode message).length ≤ 4593 := by
  have bound_crossSidesGroup := message.crossSidesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const CrossSidesGroup.encode 18 CrossSidesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CrossSidesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 CrossSidesGroup.encode CrossSidesGroup.decode CrossSidesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.crossSidesGroup.length_lt]
  rfl

end CrossSidesGroups

/-- New Order Cross Message -/
structure NewOrderCrossMessage where
  inboundBusinessHeader : InboundBusinessHeader
  offset18Padding2 : Alpha 2
  crossid : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTraderOptional : Alpha 5
  securityId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  crossedIndicator : BitVec 16
  crossSidesGroups : CrossSidesGroups
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace NewOrderCrossMessage

def encode (message : NewOrderCrossMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (Alpha.encode message.offset18Padding2
    ++ (encodeUIntLE 8 message.crossid
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTraderOptional
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 2 message.crossedIndicator
    ++ (CrossSidesGroups.encode message.crossSidesGroups
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderCrossMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (offset18Padding2, bytes) ← Alpha.decode 2 bytes
  let (crossid, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTraderOptional, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (crossedIndicator, bytes) ← decodeUIntLE 2 bytes
  let (crossSidesGroups, bytes) ← CrossSidesGroups.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, offset18Padding2, crossid, senderLocation, enteringTrader, executingTraderOptional, securityId, orderQty, price, crossedIndicator, crossSidesGroups, deskId, memo }, bytes)

theorem encode_length_pos (message : NewOrderCrossMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderCrossMessage) : (encode message).length ≤ 5179 := by
  have bound_crossSidesGroups := CrossSidesGroups.encode_length_le message.crossSidesGroups
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : NewOrderCrossMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CrossSidesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end NewOrderCrossMessage

/-- Outbound Business Header: 18 bytes -/
structure OutboundBusinessHeader where
  sessionId : BitVec 32
  msgSeqNum : BitVec 32
  sendingTime : BitVec 64
  possResend : BitVec 8
  padding : Alpha 1
  deriving DecidableEq, Repr

namespace OutboundBusinessHeader

def encode (message : OutboundBusinessHeader) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUInt 1 message.possResend
    ++ (Alpha.encode message.padding))))

def decode (bytes : List UInt8) : Option (OutboundBusinessHeader × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (possResend, bytes) ← decodeUInt 1 bytes
  let (padding, bytes) ← Alpha.decode 1 bytes
  pure ({ sessionId, msgSeqNum, sendingTime, possResend, padding }, bytes)

@[simp] theorem encode_length (message : OutboundBusinessHeader) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OutboundBusinessHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutboundBusinessHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutboundBusinessHeader

/-- Execution Report New Message -/
structure ExecutionReportNewMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  ordStatus : OrdStatus
  clordid : BitVec 64
  secondaryOrderId : BitVec 64
  securityId : BitVec 64
  orderId : BitVec 64
  account : BitVec 32
  execId : BitVec 64
  transactTime : BitVec 64
  marketSegmentReceivedTime : BitVec 64
  protectionPrice : BitVec 64
  tradeDate : BitVec 16
  workingIndicator : BitVec 8
  multiLegReportingType : MultiLegReportingType
  ordtype : Ordtype
  timeInForce : TimeInForce
  expireDate : BitVec 16
  orderQty : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  crossidOptional : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace ExecutionReportNewMessage

def encode (message : ExecutionReportNewMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.marketSegmentReceivedTime
    ++ (encodeUIntLE 8 message.protectionPrice
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.workingIndicator
    ++ (MultiLegReportingType.encode message.multiLegReportingType
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 2 message.expireDate
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (encodeUIntLE 8 message.crossidOptional
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportNewMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentReceivedTime, bytes) ← decodeUIntLE 8 bytes
  let (protectionPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (workingIndicator, bytes) ← decodeUInt 1 bytes
  let (multiLegReportingType, bytes) ← MultiLegReportingType.decode bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (crossidOptional, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ outboundBusinessHeader, side, ordStatus, clordid, secondaryOrderId, securityId, orderId, account, execId, transactTime, marketSegmentReceivedTime, protectionPrice, tradeDate, workingIndicator, multiLegReportingType, ordtype, timeInForce, expireDate, orderQty, priceOptional, stopPx, minQty, maxFloor, crossidOptional, deskId, memo }, bytes)

theorem encode_length_pos (message : ExecutionReportNewMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportNewMessage) : (encode message).length ≤ 656 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, OrdStatus.encode_length, encodeUIntLE_length, encodeUInt_length, MultiLegReportingType.encode_length, Ordtype.encode_length, TimeInForce.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MultiLegReportingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end ExecutionReportNewMessage

/-- Execution Report Modify Message -/
structure ExecutionReportModifyMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  ordStatus : OrdStatus
  clordid : BitVec 64
  secondaryOrderId : BitVec 64
  securityId : BitVec 64
  leavesQty : BitVec 64
  account : BitVec 32
  execId : BitVec 64
  transactTime : BitVec 64
  cumQty : BitVec 64
  marketSegmentReceivedTime : BitVec 64
  orderId : BitVec 64
  origclordid : BitVec 64
  protectionPrice : BitVec 64
  tradeDate : BitVec 16
  workingIndicator : BitVec 8
  multiLegReportingType : MultiLegReportingType
  ordtype : Ordtype
  timeInForce : TimeInForce
  expireDate : BitVec 16
  orderQty : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace ExecutionReportModifyMessage

def encode (message : ExecutionReportModifyMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.marketSegmentReceivedTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.origclordid
    ++ (encodeUIntLE 8 message.protectionPrice
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.workingIndicator
    ++ (MultiLegReportingType.encode message.multiLegReportingType
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 2 message.expireDate
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportModifyMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentReceivedTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (protectionPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (workingIndicator, bytes) ← decodeUInt 1 bytes
  let (multiLegReportingType, bytes) ← MultiLegReportingType.decode bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ outboundBusinessHeader, side, ordStatus, clordid, secondaryOrderId, securityId, leavesQty, account, execId, transactTime, cumQty, marketSegmentReceivedTime, orderId, origclordid, protectionPrice, tradeDate, workingIndicator, multiLegReportingType, ordtype, timeInForce, expireDate, orderQty, priceOptional, stopPx, minQty, maxFloor, deskId, memo }, bytes)

theorem encode_length_pos (message : ExecutionReportModifyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportModifyMessage) : (encode message).length ≤ 672 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, OrdStatus.encode_length, encodeUIntLE_length, encodeUInt_length, MultiLegReportingType.encode_length, Ordtype.encode_length, TimeInForce.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportModifyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MultiLegReportingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end ExecutionReportModifyMessage

/-- Execution Report Cancel Message -/
structure ExecutionReportCancelMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  ordStatus : OrdStatus
  clordid : BitVec 64
  secondaryOrderId : BitVec 64
  securityId : BitVec 64
  cumQty : BitVec 64
  account : BitVec 32
  execId : BitVec 64
  transactTime : BitVec 64
  marketSegmentReceivedTime : BitVec 64
  orderId : BitVec 64
  origclordid : BitVec 64
  tradeDate : BitVec 16
  workingIndicator : BitVec 8
  execRestatementReason : BitVec 8
  actionRequestedFromSessionId : BitVec 32
  massActionReportIdOptional : BitVec 64
  ordtype : Ordtype
  timeInForce : TimeInForce
  expireDate : BitVec 16
  orderQty : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace ExecutionReportCancelMessage

def encode (message : ExecutionReportCancelMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.marketSegmentReceivedTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.origclordid
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.workingIndicator
    ++ (encodeUInt 1 message.execRestatementReason
    ++ (encodeUIntLE 4 message.actionRequestedFromSessionId
    ++ (encodeUIntLE 8 message.massActionReportIdOptional
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 2 message.expireDate
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportCancelMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentReceivedTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (workingIndicator, bytes) ← decodeUInt 1 bytes
  let (execRestatementReason, bytes) ← decodeUInt 1 bytes
  let (actionRequestedFromSessionId, bytes) ← decodeUIntLE 4 bytes
  let (massActionReportIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ outboundBusinessHeader, side, ordStatus, clordid, secondaryOrderId, securityId, cumQty, account, execId, transactTime, marketSegmentReceivedTime, orderId, origclordid, tradeDate, workingIndicator, execRestatementReason, actionRequestedFromSessionId, massActionReportIdOptional, ordtype, timeInForce, expireDate, orderQty, priceOptional, stopPx, minQty, maxFloor, deskId, memo }, bytes)

theorem encode_length_pos (message : ExecutionReportCancelMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportCancelMessage) : (encode message).length ≤ 668 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, OrdStatus.encode_length, encodeUIntLE_length, encodeUInt_length, Ordtype.encode_length, TimeInForce.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end ExecutionReportCancelMessage

/-- Execution Report Trade Message -/
structure ExecutionReportTradeMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  ordStatus : OrdStatus
  clordidOptional : BitVec 64
  secondaryOrderId : BitVec 64
  securityId : BitVec 64
  account : BitVec 32
  lastQty : BitVec 64
  lastPx : BitVec 64
  execId : BitVec 64
  transactTime : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  aggressorIndicator : BitVec 8
  execType : ExecType
  orderCategory : OrderCategory
  multiLegReportingType : MultiLegReportingType
  tradeId : BitVec 32
  contraBroker : BitVec 32
  orderId : BitVec 64
  tradeDate : BitVec 16
  totNoRelatedSym : BitVec 8
  offset119Padding1 : Alpha 1
  secondaryExecId : BitVec 64
  execRefId : BitVec 64
  crossidOptional : BitVec 64
  crossedIndicator : BitVec 16
  orderQty : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace ExecutionReportTradeMessage

def encode (message : ExecutionReportTradeMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUIntLE 8 message.clordidOptional
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUInt 1 message.aggressorIndicator
    ++ (ExecType.encode message.execType
    ++ (OrderCategory.encode message.orderCategory
    ++ (MultiLegReportingType.encode message.multiLegReportingType
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.contraBroker
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.totNoRelatedSym
    ++ (Alpha.encode message.offset119Padding1
    ++ (encodeUIntLE 8 message.secondaryExecId
    ++ (encodeUIntLE 8 message.execRefId
    ++ (encodeUIntLE 8 message.crossidOptional
    ++ (encodeUIntLE 2 message.crossedIndicator
    ++ (encodeUIntLE 8 message.orderQty
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (clordidOptional, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderCategory, bytes) ← OrderCategory.decode bytes
  let (multiLegReportingType, bytes) ← MultiLegReportingType.decode bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (contraBroker, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (totNoRelatedSym, bytes) ← decodeUInt 1 bytes
  let (offset119Padding1, bytes) ← Alpha.decode 1 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 8 bytes
  let (execRefId, bytes) ← decodeUIntLE 8 bytes
  let (crossidOptional, bytes) ← decodeUIntLE 8 bytes
  let (crossedIndicator, bytes) ← decodeUIntLE 2 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ outboundBusinessHeader, side, ordStatus, clordidOptional, secondaryOrderId, securityId, account, lastQty, lastPx, execId, transactTime, leavesQty, cumQty, aggressorIndicator, execType, orderCategory, multiLegReportingType, tradeId, contraBroker, orderId, tradeDate, totNoRelatedSym, offset119Padding1, secondaryExecId, execRefId, crossidOptional, crossedIndicator, orderQty, deskId, memo }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeMessage) : (encode message).length ≤ 666 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, OrdStatus.encode_length, encodeUIntLE_length, encodeUInt_length, ExecType.encode_length, OrderCategory.encode_length, MultiLegReportingType.encode_length, Alpha.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MultiLegReportingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end ExecutionReportTradeMessage

/-- Text -/
structure Text where
  textData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Text

def encode (message : Text) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.textData.val.length)
    ++ (encodeMany Byte.encode message.textData.val)

def decode (bytes : List UInt8) : Option (Text × List UInt8) := do
  let (textLength, bytes) ← decodeUInt 1 bytes
  let (textData_, bytes) ← decodeMany Byte.decode textLength.toNat bytes
  if fits_textData : textData_.length < 256 ^ 1 then
    pure ({ textData := ⟨textData_, fits_textData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Text) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Text) : (encode message).length ≤ 256 := by
  have bound_textData := message.textData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Text) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.textData.length_lt]
  rfl

end Text

/-- Execution Report Reject Message -/
structure ExecutionReportRejectMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  cxlRejResponseTo : BitVec 8
  clordid : BitVec 64
  secondaryOrderIdOptional : BitVec 64
  securityId : BitVec 64
  ordRejReason : BitVec 32
  transactTime : BitVec 64
  execId : BitVec 64
  orderIdOptional : BitVec 64
  origclordid : BitVec 64
  account : BitVec 32
  ordtype : Ordtype
  timeInForce : TimeInForce
  expireDate : BitVec 16
  orderQty : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxFloor : BitVec 64
  crossidOptional : BitVec 64
  crossedIndicator : BitVec 16
  deskId : DeskId
  memo : Memo
  text : Text
  deriving DecidableEq, Repr

namespace ExecutionReportRejectMessage

def encode (message : ExecutionReportRejectMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (encodeUInt 1 message.cxlRejResponseTo
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.secondaryOrderIdOptional
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.ordRejReason
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.origclordid
    ++ (encodeUIntLE 4 message.account
    ++ (Ordtype.encode message.ordtype
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUIntLE 2 message.expireDate
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.minQty
    ++ (encodeUIntLE 8 message.maxFloor
    ++ (encodeUIntLE 8 message.crossidOptional
    ++ (encodeUIntLE 2 message.crossedIndicator
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo
    ++ (Text.encode message.text))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportRejectMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (cxlRejResponseTo, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (ordRejReason, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (origclordid, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (ordtype, bytes) ← Ordtype.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (minQty, bytes) ← decodeUIntLE 8 bytes
  let (maxFloor, bytes) ← decodeUIntLE 8 bytes
  let (crossidOptional, bytes) ← decodeUIntLE 8 bytes
  let (crossedIndicator, bytes) ← decodeUIntLE 2 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ outboundBusinessHeader, side, cxlRejResponseTo, clordid, secondaryOrderIdOptional, securityId, ordRejReason, transactTime, execId, orderIdOptional, origclordid, account, ordtype, timeInForce, expireDate, orderQty, priceOptional, stopPx, minQty, maxFloor, crossidOptional, crossedIndicator, deskId, memo, text }, bytes)

theorem encode_length_pos (message : ExecutionReportRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportRejectMessage) : (encode message).length ≤ 906 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, encodeUInt_length, encodeUIntLE_length, Ordtype.encode_length, TimeInForce.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Ordtype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Memo.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end ExecutionReportRejectMessage

/-- Execution Report Forward Message -/
structure ExecutionReportForwardMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  side : Side
  ordStatus : OrdStatus
  clordidOptional : BitVec 64
  secondaryOrderId : BitVec 64
  securityId : BitVec 64
  account : BitVec 32
  lastQty : BitVec 64
  lastPx : BitVec 64
  execId : BitVec 64
  transactTime : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  tradeId : BitVec 32
  contraBroker : BitVec 32
  orderId : BitVec 64
  aggressorIndicator : BitVec 8
  settlTypeOptional : SettlTypeOptional
  tradeDate : BitVec 16
  daysToSettlementOptional : BitVec 16
  offset118Padding2 : Alpha 2
  secondaryExecId : BitVec 64
  execRefId : BitVec 64
  fixedRateOptional : BitVec 64
  orderQty : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace ExecutionReportForwardMessage

def encode (message : ExecutionReportForwardMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Side.encode message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUIntLE 8 message.clordidOptional
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.account
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.contraBroker
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUInt 1 message.aggressorIndicator
    ++ (SettlTypeOptional.encode message.settlTypeOptional
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 2 message.daysToSettlementOptional
    ++ (Alpha.encode message.offset118Padding2
    ++ (encodeUIntLE 8 message.secondaryExecId
    ++ (encodeUIntLE 8 message.execRefId
    ++ (encodeUIntLE 8 message.fixedRateOptional
    ++ (encodeUIntLE 8 message.orderQty
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportForwardMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (clordidOptional, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (contraBroker, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  let (settlTypeOptional, bytes) ← SettlTypeOptional.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (daysToSettlementOptional, bytes) ← decodeUIntLE 2 bytes
  let (offset118Padding2, bytes) ← Alpha.decode 2 bytes
  let (secondaryExecId, bytes) ← decodeUIntLE 8 bytes
  let (execRefId, bytes) ← decodeUIntLE 8 bytes
  let (fixedRateOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ outboundBusinessHeader, side, ordStatus, clordidOptional, secondaryOrderId, securityId, account, lastQty, lastPx, execId, transactTime, leavesQty, cumQty, tradeId, contraBroker, orderId, aggressorIndicator, settlTypeOptional, tradeDate, daysToSettlementOptional, offset118Padding2, secondaryExecId, execRefId, fixedRateOptional, orderQty, deskId, memo }, bytes)

theorem encode_length_pos (message : ExecutionReportForwardMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportForwardMessage) : (encode message).length ≤ 664 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, Side.encode_length, OrdStatus.encode_length, encodeUIntLE_length, encodeUInt_length, SettlTypeOptional.encode_length, Alpha.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportForwardMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SettlTypeOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end ExecutionReportForwardMessage

/-- Business Message Reject Message -/
structure BusinessMessageRejectMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  refMsgType : BitVec 8
  offset19Padding1 : Alpha 1
  refSeqNum : BitVec 32
  businessRejectRefId : BitVec 64
  businessRejectReason : BitVec 32
  memo : Memo
  text : Text
  deriving DecidableEq, Repr

namespace BusinessMessageRejectMessage

def encode (message : BusinessMessageRejectMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (encodeUInt 1 message.refMsgType
    ++ (Alpha.encode message.offset19Padding1
    ++ (encodeUIntLE 4 message.refSeqNum
    ++ (encodeUIntLE 8 message.businessRejectRefId
    ++ (encodeUIntLE 4 message.businessRejectReason
    ++ (Memo.encode message.memo
    ++ (Text.encode message.text)))))))

def decode (bytes : List UInt8) : Option (BusinessMessageRejectMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (refMsgType, bytes) ← decodeUInt 1 bytes
  let (offset19Padding1, bytes) ← Alpha.decode 1 bytes
  let (refSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (businessRejectRefId, bytes) ← decodeUIntLE 8 bytes
  let (businessRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (memo, bytes) ← Memo.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ outboundBusinessHeader, refMsgType, offset19Padding1, refSeqNum, businessRejectRefId, businessRejectReason, memo, text }, bytes)

theorem encode_length_pos (message : BusinessMessageRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BusinessMessageRejectMessage) : (encode message).length ≤ 548 := by
  have bound_memo := Memo.encode_length_le message.memo
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : BusinessMessageRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Memo.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end BusinessMessageRejectMessage

/-- Legs Group: 30 bytes -/
structure LegsGroup where
  legSymbol : Alpha 20
  legRatioQty : BitVec 64
  legSide : LegSide
  padding1 : Alpha 1
  deriving DecidableEq, Repr

namespace LegsGroup

def encode (message : LegsGroup) : List UInt8 :=
  Alpha.encode message.legSymbol
    ++ (encodeUIntLE 8 message.legRatioQty
    ++ (LegSide.encode message.legSide
    ++ (Alpha.encode message.padding1)))

def decode (bytes : List UInt8) : Option (LegsGroup × List UInt8) := do
  let (legSymbol, bytes) ← Alpha.decode 20 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 8 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (padding1, bytes) ← Alpha.decode 1 bytes
  pure ({ legSymbol, legRatioQty, legSide, padding1 }, bytes)

@[simp] theorem encode_length (message : LegsGroup) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, LegSide.encode_length]

theorem encode_length_pos (message : LegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegsGroup

/-- Legs Groups -/
structure LegsGroups where
  blockLength : BitVec 16
  legsGroup : Bounded 1 LegsGroup
  deriving DecidableEq, Repr

namespace LegsGroups

def encode (message : LegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legsGroup.val.length)
    ++ (encodeMany LegsGroup.encode message.legsGroup.val))

def decode (bytes : List UInt8) : Option (LegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (legsGroup_, bytes) ← decodeMany LegsGroup.decode numInGroup.toNat bytes
  if fits_legsGroup : legsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, legsGroup := ⟨legsGroup_, fits_legsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegsGroups) : (encode message).length ≤ 7653 := by
  have bound_legsGroup := message.legsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegsGroup.encode 30 LegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegsGroup.encode LegsGroup.decode LegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legsGroup.length_lt]
  rfl

end LegsGroups

/-- Security Definition Request Message -/
structure SecurityDefinitionRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  securityReqId : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  legsGroups : LegsGroups
  deriving DecidableEq, Repr

namespace SecurityDefinitionRequestMessage

def encode (message : SecurityDefinitionRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUIntLE 8 message.securityReqId
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (LegsGroups.encode message.legsGroups))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (securityReqId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (legsGroups, bytes) ← LegsGroups.decode bytes
  pure ({ inboundBusinessHeader, securityReqId, senderLocation, enteringTrader, legsGroups }, bytes)

theorem encode_length_pos (message : SecurityDefinitionRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionRequestMessage) : (encode message).length ≤ 7694 := by
  have bound_legsGroups := LegsGroups.encode_length_le message.legsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [LegsGroups.decode_encode, some_bind]
  rfl

end SecurityDefinitionRequestMessage

/-- Security Definition Response Message: 83 bytes -/
structure SecurityDefinitionResponseMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  offset18Padding2 : Alpha 2
  securityReqId : BitVec 64
  securityId : BitVec 64
  securityResponseType : BitVec 8
  securityStrategyType : Alpha 3
  symbol : Alpha 20
  securityResponseId : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  deriving DecidableEq, Repr

namespace SecurityDefinitionResponseMessage

def encode (message : SecurityDefinitionResponseMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (Alpha.encode message.offset18Padding2
    ++ (encodeUIntLE 8 message.securityReqId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUInt 1 message.securityResponseType
    ++ (Alpha.encode message.securityStrategyType
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.securityResponseId
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader)))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionResponseMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (offset18Padding2, bytes) ← Alpha.decode 2 bytes
  let (securityReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (securityResponseType, bytes) ← decodeUInt 1 bytes
  let (securityStrategyType, bytes) ← Alpha.decode 3 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  pure ({ outboundBusinessHeader, offset18Padding2, securityReqId, securityId, securityResponseType, securityStrategyType, symbol, securityResponseId, senderLocation, enteringTrader }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionResponseMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, OutboundBusinessHeader.encode_length, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityDefinitionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityDefinitionResponseMessage

/-- Bidirectional Business Header: 19 bytes -/
structure BidirectionalBusinessHeader where
  sessionId : BitVec 32
  msgSeqNum : BitVec 32
  sendingTime : BitVec 64
  possResend : BitVec 8
  marketSegmentIdOptional : BitVec 8
  padding : Alpha 1
  deriving DecidableEq, Repr

namespace BidirectionalBusinessHeader

def encode (message : BidirectionalBusinessHeader) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUInt 1 message.possResend
    ++ (encodeUInt 1 message.marketSegmentIdOptional
    ++ (Alpha.encode message.padding)))))

def decode (bytes : List UInt8) : Option (BidirectionalBusinessHeader × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (possResend, bytes) ← decodeUInt 1 bytes
  let (marketSegmentIdOptional, bytes) ← decodeUInt 1 bytes
  let (padding, bytes) ← Alpha.decode 1 bytes
  pure ({ sessionId, msgSeqNum, sendingTime, possResend, marketSegmentIdOptional, padding }, bytes)

@[simp] theorem encode_length (message : BidirectionalBusinessHeader) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BidirectionalBusinessHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidirectionalBusinessHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BidirectionalBusinessHeader

/-- Sides Group: 5 bytes -/
structure SidesGroup where
  side : Side
  account : BitVec 32
  deriving DecidableEq, Repr

namespace SidesGroup

def encode (message : SidesGroup) : List UInt8 :=
  Side.encode message.side
    ++ (encodeUIntLE 4 message.account)

def decode (bytes : List UInt8) : Option (SidesGroup × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  pure ({ side, account }, bytes)

@[simp] theorem encode_length (message : SidesGroup) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Side.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SidesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SidesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SidesGroup

/-- Sides Groups -/
structure SidesGroups where
  blockLength : BitVec 16
  sidesGroup : Bounded 1 SidesGroup
  deriving DecidableEq, Repr

namespace SidesGroups

def encode (message : SidesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sidesGroup.val.length)
    ++ (encodeMany SidesGroup.encode message.sidesGroup.val))

def decode (bytes : List UInt8) : Option (SidesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (sidesGroup_, bytes) ← decodeMany SidesGroup.decode numInGroup.toNat bytes
  if fits_sidesGroup : sidesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, sidesGroup := ⟨sidesGroup_, fits_sidesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SidesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SidesGroups) : (encode message).length ≤ 1278 := by
  have bound_sidesGroup := message.sidesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SidesGroup.encode 5 SidesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SidesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SidesGroup.encode SidesGroup.decode SidesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sidesGroup.length_lt]
  rfl

end SidesGroups

/-- Quote Req Id -/
structure QuoteReqId where
  quoteReqIdData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace QuoteReqId

def encode (message : QuoteReqId) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteReqIdData.val.length)
    ++ (encodeMany Byte.encode message.quoteReqIdData.val)

def decode (bytes : List UInt8) : Option (QuoteReqId × List UInt8) := do
  let (quoteReqIdLength, bytes) ← decodeUInt 1 bytes
  let (quoteReqIdData_, bytes) ← decodeMany Byte.decode quoteReqIdLength.toNat bytes
  if fits_quoteReqIdData : quoteReqIdData_.length < 256 ^ 1 then
    pure ({ quoteReqIdData := ⟨quoteReqIdData_, fits_quoteReqIdData⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteReqId) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteReqId) : (encode message).length ≤ 256 := by
  have bound_quoteReqIdData := message.quoteReqIdData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteReqId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteReqIdData.length_lt]
  rfl

end QuoteReqId

/-- Quote Request Message -/
structure QuoteRequestMessage where
  bidirectionalBusinessHeader : BidirectionalBusinessHeader
  securityId : BitVec 64
  quoteIdOptional : BitVec 64
  tradeIdOptional : BitVec 32
  contraBroker : BitVec 32
  transactTime : BitVec 64
  price : BitVec 64
  settlType : SettlType
  executeUnderlyingTrade : ExecuteUnderlyingTrade
  orderQty : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTrader : Alpha 5
  fixedRate : BitVec 64
  daysToSettlement : BitVec 16
  sidesGroups : SidesGroups
  quoteReqId : QuoteReqId
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace QuoteRequestMessage

def encode (message : QuoteRequestMessage) : List UInt8 :=
  BidirectionalBusinessHeader.encode message.bidirectionalBusinessHeader
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteIdOptional
    ++ (encodeUIntLE 4 message.tradeIdOptional
    ++ (encodeUIntLE 4 message.contraBroker
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.price
    ++ (SettlType.encode message.settlType
    ++ (ExecuteUnderlyingTrade.encode message.executeUnderlyingTrade
    ++ (encodeUIntLE 8 message.orderQty
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTrader
    ++ (encodeUIntLE 8 message.fixedRate
    ++ (encodeUIntLE 2 message.daysToSettlement
    ++ (SidesGroups.encode message.sidesGroups
    ++ (QuoteReqId.encode message.quoteReqId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteRequestMessage × List UInt8) := do
  let (bidirectionalBusinessHeader, bytes) ← BidirectionalBusinessHeader.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (contraBroker, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (executeUnderlyingTrade, bytes) ← ExecuteUnderlyingTrade.decode bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTrader, bytes) ← Alpha.decode 5 bytes
  let (fixedRate, bytes) ← decodeUIntLE 8 bytes
  let (daysToSettlement, bytes) ← decodeUIntLE 2 bytes
  let (sidesGroups, bytes) ← SidesGroups.decode bytes
  let (quoteReqId, bytes) ← QuoteReqId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ bidirectionalBusinessHeader, securityId, quoteIdOptional, tradeIdOptional, contraBroker, transactTime, price, settlType, executeUnderlyingTrade, orderQty, senderLocation, enteringTrader, executingTrader, fixedRate, daysToSettlement, sidesGroups, quoteReqId, deskId, memo }, bytes)

theorem encode_length_pos (message : QuoteRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [BidirectionalBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequestMessage) : (encode message).length ≤ 2145 := by
  have bound_sidesGroups := SidesGroups.encode_length_le message.sidesGroups
  have bound_quoteReqId := QuoteReqId.encode_length_le message.quoteReqId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, BidirectionalBusinessHeader.encode_length, encodeUIntLE_length, SettlType.encode_length, ExecuteUnderlyingTrade.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BidirectionalBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecuteUnderlyingTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SidesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteReqId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end QuoteRequestMessage

/-- Quote Status Report Message -/
structure QuoteStatusReportMessage where
  bidirectionalBusinessHeader : BidirectionalBusinessHeader
  quoteRejectReason : BitVec 32
  securityId : BitVec 64
  quoteId : BitVec 64
  tradeIdOptional : BitVec 32
  contraBroker : BitVec 32
  transactTime : BitVec 64
  quoteStatus : BitVec 8
  quoteStatusResponseTo : QuoteStatusResponseTo
  account : BitVec 32
  sideOptional : SideOptional
  settlTypeOptional : SettlTypeOptional
  priceOptional : BitVec 64
  orderQty : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTrader : Alpha 5
  fixedRateOptional : BitVec 64
  executeUnderlyingTrade : ExecuteUnderlyingTrade
  daysToSettlementOptional : BitVec 16
  quoteReqId : QuoteReqId
  deskId : DeskId
  memo : Memo
  text : Text
  deriving DecidableEq, Repr

namespace QuoteStatusReportMessage

def encode (message : QuoteStatusReportMessage) : List UInt8 :=
  BidirectionalBusinessHeader.encode message.bidirectionalBusinessHeader
    ++ (encodeUIntLE 4 message.quoteRejectReason
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.tradeIdOptional
    ++ (encodeUIntLE 4 message.contraBroker
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUInt 1 message.quoteStatus
    ++ (QuoteStatusResponseTo.encode message.quoteStatusResponseTo
    ++ (encodeUIntLE 4 message.account
    ++ (SideOptional.encode message.sideOptional
    ++ (SettlTypeOptional.encode message.settlTypeOptional
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.orderQty
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTrader
    ++ (encodeUIntLE 8 message.fixedRateOptional
    ++ (ExecuteUnderlyingTrade.encode message.executeUnderlyingTrade
    ++ (encodeUIntLE 2 message.daysToSettlementOptional
    ++ (QuoteReqId.encode message.quoteReqId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo
    ++ (Text.encode message.text)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteStatusReportMessage × List UInt8) := do
  let (bidirectionalBusinessHeader, bytes) ← BidirectionalBusinessHeader.decode bytes
  let (quoteRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (contraBroker, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (quoteStatusResponseTo, bytes) ← QuoteStatusResponseTo.decode bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (settlTypeOptional, bytes) ← SettlTypeOptional.decode bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTrader, bytes) ← Alpha.decode 5 bytes
  let (fixedRateOptional, bytes) ← decodeUIntLE 8 bytes
  let (executeUnderlyingTrade, bytes) ← ExecuteUnderlyingTrade.decode bytes
  let (daysToSettlementOptional, bytes) ← decodeUIntLE 2 bytes
  let (quoteReqId, bytes) ← QuoteReqId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ bidirectionalBusinessHeader, quoteRejectReason, securityId, quoteId, tradeIdOptional, contraBroker, transactTime, quoteStatus, quoteStatusResponseTo, account, sideOptional, settlTypeOptional, priceOptional, orderQty, senderLocation, enteringTrader, executingTrader, fixedRateOptional, executeUnderlyingTrade, daysToSettlementOptional, quoteReqId, deskId, memo, text }, bytes)

theorem encode_length_pos (message : QuoteStatusReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [BidirectionalBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteStatusReportMessage) : (encode message).length ≤ 1134 := by
  have bound_quoteReqId := QuoteReqId.encode_length_le message.quoteReqId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, BidirectionalBusinessHeader.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteStatusResponseTo.encode_length, SideOptional.encode_length, SettlTypeOptional.encode_length, Alpha.encode_length, ExecuteUnderlyingTrade.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteStatusReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BidirectionalBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteStatusResponseTo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlTypeOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExecuteUnderlyingTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteReqId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Memo.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end QuoteStatusReportMessage

/-- Quote Message -/
structure QuoteMessage where
  bidirectionalBusinessHeader : BidirectionalBusinessHeader
  securityId : BitVec 64
  quoteId : BitVec 64
  transactTime : BitVec 64
  priceOptional : BitVec 64
  orderQty : BitVec 64
  side : Side
  settlType : SettlType
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTrader : Alpha 5
  fixedRate : BitVec 64
  executeUnderlyingTrade : ExecuteUnderlyingTrade
  daysToSettlement : BitVec 16
  quoteReqId : QuoteReqId
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  BidirectionalBusinessHeader.encode message.bidirectionalBusinessHeader
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.orderQty
    ++ (Side.encode message.side
    ++ (SettlType.encode message.settlType
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTrader
    ++ (encodeUIntLE 8 message.fixedRate
    ++ (ExecuteUnderlyingTrade.encode message.executeUnderlyingTrade
    ++ (encodeUIntLE 2 message.daysToSettlement
    ++ (QuoteReqId.encode message.quoteReqId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (bidirectionalBusinessHeader, bytes) ← BidirectionalBusinessHeader.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTrader, bytes) ← Alpha.decode 5 bytes
  let (fixedRate, bytes) ← decodeUIntLE 8 bytes
  let (executeUnderlyingTrade, bytes) ← ExecuteUnderlyingTrade.decode bytes
  let (daysToSettlement, bytes) ← decodeUIntLE 2 bytes
  let (quoteReqId, bytes) ← QuoteReqId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ bidirectionalBusinessHeader, securityId, quoteId, transactTime, priceOptional, orderQty, side, settlType, account, senderLocation, enteringTrader, executingTrader, fixedRate, executeUnderlyingTrade, daysToSettlement, quoteReqId, deskId, memo }, bytes)

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [BidirectionalBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 864 := by
  have bound_quoteReqId := QuoteReqId.encode_length_le message.quoteReqId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, BidirectionalBusinessHeader.encode_length, encodeUIntLE_length, Side.encode_length, SettlType.encode_length, Alpha.encode_length, ExecuteUnderlyingTrade.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BidirectionalBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExecuteUnderlyingTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteReqId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Quote Cancel Message -/
structure QuoteCancelMessage where
  bidirectionalBusinessHeader : BidirectionalBusinessHeader
  securityId : BitVec 64
  quoteIdOptional : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  executingTrader : Alpha 5
  quoteReqId : QuoteReqId
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace QuoteCancelMessage

def encode (message : QuoteCancelMessage) : List UInt8 :=
  BidirectionalBusinessHeader.encode message.bidirectionalBusinessHeader
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteIdOptional
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (Alpha.encode message.executingTrader
    ++ (QuoteReqId.encode message.quoteReqId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))

def decode (bytes : List UInt8) : Option (QuoteCancelMessage × List UInt8) := do
  let (bidirectionalBusinessHeader, bytes) ← BidirectionalBusinessHeader.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (executingTrader, bytes) ← Alpha.decode 5 bytes
  let (quoteReqId, bytes) ← QuoteReqId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ bidirectionalBusinessHeader, securityId, quoteIdOptional, account, senderLocation, enteringTrader, executingTrader, quoteReqId, deskId, memo }, bytes)

theorem encode_length_pos (message : QuoteCancelMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [BidirectionalBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelMessage) : (encode message).length ≤ 827 := by
  have bound_quoteReqId := QuoteReqId.encode_length_le message.quoteReqId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, BidirectionalBusinessHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BidirectionalBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteReqId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end QuoteCancelMessage

/-- Quote Request Reject Message -/
structure QuoteRequestRejectMessage where
  bidirectionalBusinessHeader : BidirectionalBusinessHeader
  quoteRequestRejectReason : BitVec 32
  securityId : BitVec 64
  quoteIdOptional : BitVec 64
  tradeIdOptional : BitVec 32
  contraBroker : BitVec 32
  transactTime : BitVec 64
  enteringTrader : Alpha 5
  settlTypeOptional : SettlTypeOptional
  priceOptional : BitVec 64
  orderQtyOptional : BitVec 64
  senderLocation : Alpha 10
  executingTrader : Alpha 5
  fixedRateOptional : BitVec 64
  daysToSettlementOptional : BitVec 16
  sidesGroups : SidesGroups
  quoteReqId : QuoteReqId
  deskId : DeskId
  memo : Memo
  text : Text
  deriving DecidableEq, Repr

namespace QuoteRequestRejectMessage

def encode (message : QuoteRequestRejectMessage) : List UInt8 :=
  BidirectionalBusinessHeader.encode message.bidirectionalBusinessHeader
    ++ (encodeUIntLE 4 message.quoteRequestRejectReason
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteIdOptional
    ++ (encodeUIntLE 4 message.tradeIdOptional
    ++ (encodeUIntLE 4 message.contraBroker
    ++ (encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.enteringTrader
    ++ (SettlTypeOptional.encode message.settlTypeOptional
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.orderQtyOptional
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.executingTrader
    ++ (encodeUIntLE 8 message.fixedRateOptional
    ++ (encodeUIntLE 2 message.daysToSettlementOptional
    ++ (SidesGroups.encode message.sidesGroups
    ++ (QuoteReqId.encode message.quoteReqId
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo
    ++ (Text.encode message.text)))))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteRequestRejectMessage × List UInt8) := do
  let (bidirectionalBusinessHeader, bytes) ← BidirectionalBusinessHeader.decode bytes
  let (quoteRequestRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (contraBroker, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (settlTypeOptional, bytes) ← SettlTypeOptional.decode bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQtyOptional, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (executingTrader, bytes) ← Alpha.decode 5 bytes
  let (fixedRateOptional, bytes) ← decodeUIntLE 8 bytes
  let (daysToSettlementOptional, bytes) ← decodeUIntLE 2 bytes
  let (sidesGroups, bytes) ← SidesGroups.decode bytes
  let (quoteReqId, bytes) ← QuoteReqId.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ bidirectionalBusinessHeader, quoteRequestRejectReason, securityId, quoteIdOptional, tradeIdOptional, contraBroker, transactTime, enteringTrader, settlTypeOptional, priceOptional, orderQtyOptional, senderLocation, executingTrader, fixedRateOptional, daysToSettlementOptional, sidesGroups, quoteReqId, deskId, memo, text }, bytes)

theorem encode_length_pos (message : QuoteRequestRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [BidirectionalBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequestRejectMessage) : (encode message).length ≤ 2404 := by
  have bound_sidesGroups := SidesGroups.encode_length_le message.sidesGroups
  have bound_quoteReqId := QuoteReqId.encode_length_le message.quoteReqId
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, BidirectionalBusinessHeader.encode_length, encodeUIntLE_length, Alpha.encode_length, SettlTypeOptional.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequestRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BidirectionalBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlTypeOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SidesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteReqId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Memo.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end QuoteRequestRejectMessage

/-- Position Maintenance Cancel Request Message: 65 bytes -/
structure PositionMaintenanceCancelRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  posReqId : BitVec 64
  securityId : BitVec 64
  origPosReqRefId : BitVec 64
  posMaintRptRefId : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  deriving DecidableEq, Repr

namespace PositionMaintenanceCancelRequestMessage

def encode (message : PositionMaintenanceCancelRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUIntLE 8 message.posReqId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.origPosReqRefId
    ++ (encodeUIntLE 8 message.posMaintRptRefId
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader))))))

def decode (bytes : List UInt8) : Option (PositionMaintenanceCancelRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (posReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (origPosReqRefId, bytes) ← decodeUIntLE 8 bytes
  let (posMaintRptRefId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  pure ({ inboundBusinessHeader, posReqId, securityId, origPosReqRefId, posMaintRptRefId, senderLocation, enteringTrader }, bytes)

@[simp] theorem encode_length (message : PositionMaintenanceCancelRequestMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, InboundBusinessHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : PositionMaintenanceCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PositionMaintenanceCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PositionMaintenanceCancelRequestMessage

/-- Position Maintenance Request Message -/
structure PositionMaintenanceRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  posReqId : BitVec 64
  securityId : BitVec 64
  thresholdAmount : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  posTransType : BitVec 8
  clearingBusinessDate : BitVec 16
  contraryInstructionIndicator : BitVec 8
  enteringTrader : Alpha 5
  longQty : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace PositionMaintenanceRequestMessage

def encode (message : PositionMaintenanceRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUIntLE 8 message.posReqId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.thresholdAmount
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (encodeUInt 1 message.posTransType
    ++ (encodeUIntLE 2 message.clearingBusinessDate
    ++ (encodeUInt 1 message.contraryInstructionIndicator
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUIntLE 8 message.longQty
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo))))))))))))

def decode (bytes : List UInt8) : Option (PositionMaintenanceRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (posReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (thresholdAmount, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (posTransType, bytes) ← decodeUInt 1 bytes
  let (clearingBusinessDate, bytes) ← decodeUIntLE 2 bytes
  let (contraryInstructionIndicator, bytes) ← decodeUInt 1 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (longQty, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, posReqId, securityId, thresholdAmount, account, senderLocation, posTransType, clearingBusinessDate, contraryInstructionIndicator, enteringTrader, longQty, deskId, memo }, bytes)

theorem encode_length_pos (message : PositionMaintenanceRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PositionMaintenanceRequestMessage) : (encode message).length ≤ 585 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : PositionMaintenanceRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end PositionMaintenanceRequestMessage

/-- Positions Group: 17 bytes -/
structure PositionsGroup where
  posType : PosType
  longQtyOptional : BitVec 64
  shortQty : BitVec 64
  deriving DecidableEq, Repr

namespace PositionsGroup

def encode (message : PositionsGroup) : List UInt8 :=
  PosType.encode message.posType
    ++ (encodeUIntLE 8 message.longQtyOptional
    ++ (encodeUIntLE 8 message.shortQty))

def decode (bytes : List UInt8) : Option (PositionsGroup × List UInt8) := do
  let (posType, bytes) ← PosType.decode bytes
  let (longQtyOptional, bytes) ← decodeUIntLE 8 bytes
  let (shortQty, bytes) ← decodeUIntLE 8 bytes
  pure ({ posType, longQtyOptional, shortQty }, bytes)

@[simp] theorem encode_length (message : PositionsGroup) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, PosType.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PositionsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PositionsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, PosType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PositionsGroup

/-- Positions Groups -/
structure PositionsGroups where
  blockLength : BitVec 16
  positionsGroup : Bounded 1 PositionsGroup
  deriving DecidableEq, Repr

namespace PositionsGroups

def encode (message : PositionsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.positionsGroup.val.length)
    ++ (encodeMany PositionsGroup.encode message.positionsGroup.val))

def decode (bytes : List UInt8) : Option (PositionsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (positionsGroup_, bytes) ← decodeMany PositionsGroup.decode numInGroup.toNat bytes
  if fits_positionsGroup : positionsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, positionsGroup := ⟨positionsGroup_, fits_positionsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PositionsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PositionsGroups) : (encode message).length ≤ 4338 := by
  have bound_positionsGroup := message.positionsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const PositionsGroup.encode 17 PositionsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PositionsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PositionsGroup.encode PositionsGroup.decode PositionsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.positionsGroup.length_lt]
  rfl

end PositionsGroups

/-- Position Maintenance Report Message -/
structure PositionMaintenanceReportMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  posReqIdOptional : BitVec 64
  securityId : BitVec 64
  posMaintRptId : BitVec 64
  posTransType : BitVec 8
  posMaintAction : PosMaintAction
  posMaintStatus : PosMaintStatus
  tradeIdOptional : BitVec 32
  origPosReqRefId : BitVec 64
  accountType : BitVec 8
  clearingBusinessDate : BitVec 16
  thresholdAmount : BitVec 64
  transactTime : BitVec 64
  account : BitVec 32
  senderLocation : Alpha 10
  posMaintResult : BitVec 32
  contraryInstructionIndicator : BitVec 8
  positionsGroups : PositionsGroups
  deskId : DeskId
  memo : Memo
  text : Text
  deriving DecidableEq, Repr

namespace PositionMaintenanceReportMessage

def encode (message : PositionMaintenanceReportMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (encodeUIntLE 8 message.posReqIdOptional
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.posMaintRptId
    ++ (encodeUInt 1 message.posTransType
    ++ (PosMaintAction.encode message.posMaintAction
    ++ (PosMaintStatus.encode message.posMaintStatus
    ++ (encodeUIntLE 4 message.tradeIdOptional
    ++ (encodeUIntLE 8 message.origPosReqRefId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUIntLE 2 message.clearingBusinessDate
    ++ (encodeUIntLE 8 message.thresholdAmount
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.account
    ++ (Alpha.encode message.senderLocation
    ++ (encodeUIntLE 4 message.posMaintResult
    ++ (encodeUInt 1 message.contraryInstructionIndicator
    ++ (PositionsGroups.encode message.positionsGroups
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo
    ++ (Text.encode message.text))))))))))))))))))))

def decode (bytes : List UInt8) : Option (PositionMaintenanceReportMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (posReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (posMaintRptId, bytes) ← decodeUIntLE 8 bytes
  let (posTransType, bytes) ← decodeUInt 1 bytes
  let (posMaintAction, bytes) ← PosMaintAction.decode bytes
  let (posMaintStatus, bytes) ← PosMaintStatus.decode bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (origPosReqRefId, bytes) ← decodeUIntLE 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (clearingBusinessDate, bytes) ← decodeUIntLE 2 bytes
  let (thresholdAmount, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← decodeUIntLE 4 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (posMaintResult, bytes) ← decodeUIntLE 4 bytes
  let (contraryInstructionIndicator, bytes) ← decodeUInt 1 bytes
  let (positionsGroups, bytes) ← PositionsGroups.decode bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ outboundBusinessHeader, posReqIdOptional, securityId, posMaintRptId, posTransType, posMaintAction, posMaintStatus, tradeIdOptional, origPosReqRefId, accountType, clearingBusinessDate, thresholdAmount, transactTime, account, senderLocation, posMaintResult, contraryInstructionIndicator, positionsGroups, deskId, memo, text }, bytes)

theorem encode_length_pos (message : PositionMaintenanceReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PositionMaintenanceReportMessage) : (encode message).length ≤ 5201 := by
  have bound_positionsGroups := PositionsGroups.encode_length_le message.positionsGroups
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, encodeUIntLE_length, encodeUInt_length, PosMaintAction.encode_length, PosMaintStatus.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : PositionMaintenanceReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PosMaintAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PosMaintStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Memo.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end PositionMaintenanceReportMessage

/-- Allocation Instruction Message -/
structure AllocationInstructionMessage where
  inboundBusinessHeader : InboundBusinessHeader
  allocId : BitVec 64
  securityId : BitVec 64
  allocTransType : AllocTransType
  allocType : AllocType
  allocNoOrdersType : AllocNoOrdersType
  quantity : BitVec 64
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  tradeId : BitVec 32
  tradeDateOptional : BitVec 16
  individualAllocId : BitVec 64
  allocAccount : BitVec 32
  allocQty : BitVec 64
  deskId : DeskId
  memo : Memo
  deriving DecidableEq, Repr

namespace AllocationInstructionMessage

def encode (message : AllocationInstructionMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUIntLE 8 message.allocId
    ++ (encodeUIntLE 8 message.securityId
    ++ (AllocTransType.encode message.allocTransType
    ++ (AllocType.encode message.allocType
    ++ (AllocNoOrdersType.encode message.allocNoOrdersType
    ++ (encodeUIntLE 8 message.quantity
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 2 message.tradeDateOptional
    ++ (encodeUIntLE 8 message.individualAllocId
    ++ (encodeUIntLE 4 message.allocAccount
    ++ (encodeUIntLE 8 message.allocQty
    ++ (DeskId.encode message.deskId
    ++ (Memo.encode message.memo)))))))))))))))

def decode (bytes : List UInt8) : Option (AllocationInstructionMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (allocId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (allocTransType, bytes) ← AllocTransType.decode bytes
  let (allocType, bytes) ← AllocType.decode bytes
  let (allocNoOrdersType, bytes) ← AllocNoOrdersType.decode bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDateOptional, bytes) ← decodeUIntLE 2 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 8 bytes
  let (allocAccount, bytes) ← decodeUIntLE 4 bytes
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (deskId, bytes) ← DeskId.decode bytes
  let (memo, bytes) ← Memo.decode bytes
  pure ({ inboundBusinessHeader, allocId, securityId, allocTransType, allocType, allocNoOrdersType, quantity, senderLocation, enteringTrader, tradeId, tradeDateOptional, individualAllocId, allocAccount, allocQty, deskId, memo }, bytes)

theorem encode_length_pos (message : AllocationInstructionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AllocationInstructionMessage) : (encode message).length ≤ 598 := by
  have bound_deskId := DeskId.encode_length_le message.deskId
  have bound_memo := Memo.encode_length_le message.memo
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, InboundBusinessHeader.encode_length, encodeUIntLE_length, AllocTransType.encode_length, AllocType.encode_length, AllocNoOrdersType.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : AllocationInstructionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AllocTransType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllocType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllocNoOrdersType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, DeskId.decode_encode, some_bind]
  dsimp only
  rw [Memo.decode_encode, some_bind]
  rfl

end AllocationInstructionMessage

/-- Allocation Report Message: 84 bytes -/
structure AllocationReportMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  allocId : BitVec 64
  securityId : BitVec 64
  allocReportId : BitVec 64
  allocTransType : AllocTransType
  allocReportType : AllocReportType
  allocNoOrdersType : AllocNoOrdersType
  allocRejCode : BitVec 32
  quantity : BitVec 64
  allocStatus : AllocStatus
  tradeDateOptional : BitVec 16
  transactTime : BitVec 64
  side : Side
  senderLocation : Alpha 10
  enteringTrader : Alpha 5
  deriving DecidableEq, Repr

namespace AllocationReportMessage

def encode (message : AllocationReportMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (encodeUIntLE 8 message.allocId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.allocReportId
    ++ (AllocTransType.encode message.allocTransType
    ++ (AllocReportType.encode message.allocReportType
    ++ (AllocNoOrdersType.encode message.allocNoOrdersType
    ++ (encodeUIntLE 4 message.allocRejCode
    ++ (encodeUIntLE 8 message.quantity
    ++ (AllocStatus.encode message.allocStatus
    ++ (encodeUIntLE 2 message.tradeDateOptional
    ++ (encodeUIntLE 8 message.transactTime
    ++ (Side.encode message.side
    ++ (Alpha.encode message.senderLocation
    ++ (Alpha.encode message.enteringTrader))))))))))))))

def decode (bytes : List UInt8) : Option (AllocationReportMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (allocId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (allocReportId, bytes) ← decodeUIntLE 8 bytes
  let (allocTransType, bytes) ← AllocTransType.decode bytes
  let (allocReportType, bytes) ← AllocReportType.decode bytes
  let (allocNoOrdersType, bytes) ← AllocNoOrdersType.decode bytes
  let (allocRejCode, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (allocStatus, bytes) ← AllocStatus.decode bytes
  let (tradeDateOptional, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (senderLocation, bytes) ← Alpha.decode 10 bytes
  let (enteringTrader, bytes) ← Alpha.decode 5 bytes
  pure ({ outboundBusinessHeader, allocId, securityId, allocReportId, allocTransType, allocReportType, allocNoOrdersType, allocRejCode, quantity, allocStatus, tradeDateOptional, transactTime, side, senderLocation, enteringTrader }, bytes)

@[simp] theorem encode_length (message : AllocationReportMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, OutboundBusinessHeader.encode_length, encodeUIntLE_length, AllocTransType.encode_length, AllocReportType.encode_length, AllocNoOrdersType.encode_length, AllocStatus.encode_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AllocationReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AllocationReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AllocTransType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllocReportType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllocNoOrdersType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AllocStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AllocationReportMessage

/-- Order Mass Action Request Message: 54 bytes -/
structure OrderMassActionRequestMessage where
  inboundBusinessHeader : InboundBusinessHeader
  massActionType : BitVec 8
  massActionScope : BitVec 8
  clordid : BitVec 64
  massCancelRestatementReason : BitVec 8
  ordtagid : BitVec 8
  sideOptional : SideOptional
  offset31Padding1 : Alpha 1
  asset : Alpha 6
  securityIdOptional : BitVec 64
  actionTargetSessionId : BitVec 32
  actionTargetGroupId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderMassActionRequestMessage

def encode (message : OrderMassActionRequestMessage) : List UInt8 :=
  InboundBusinessHeader.encode message.inboundBusinessHeader
    ++ (encodeUInt 1 message.massActionType
    ++ (encodeUInt 1 message.massActionScope
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUInt 1 message.massCancelRestatementReason
    ++ (encodeUInt 1 message.ordtagid
    ++ (SideOptional.encode message.sideOptional
    ++ (Alpha.encode message.offset31Padding1
    ++ (Alpha.encode message.asset
    ++ (encodeUIntLE 8 message.securityIdOptional
    ++ (encodeUIntLE 4 message.actionTargetSessionId
    ++ (encodeUIntLE 4 message.actionTargetGroupId)))))))))))

def decode (bytes : List UInt8) : Option (OrderMassActionRequestMessage × List UInt8) := do
  let (inboundBusinessHeader, bytes) ← InboundBusinessHeader.decode bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionScope, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRestatementReason, bytes) ← decodeUInt 1 bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (offset31Padding1, bytes) ← Alpha.decode 1 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (actionTargetSessionId, bytes) ← decodeUIntLE 4 bytes
  let (actionTargetGroupId, bytes) ← decodeUIntLE 4 bytes
  pure ({ inboundBusinessHeader, massActionType, massActionScope, clordid, massCancelRestatementReason, ordtagid, sideOptional, offset31Padding1, asset, securityIdOptional, actionTargetSessionId, actionTargetGroupId }, bytes)

@[simp] theorem encode_length (message : OrderMassActionRequestMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, InboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, SideOptional.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassActionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassActionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, InboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMassActionRequestMessage

/-- Comp Ids Group: 4 bytes -/
structure CompIdsGroup where
  refCompId : BitVec 32
  deriving DecidableEq, Repr

namespace CompIdsGroup

def encode (message : CompIdsGroup) : List UInt8 :=
  encodeUIntLE 4 message.refCompId

def decode (bytes : List UInt8) : Option (CompIdsGroup × List UInt8) := do
  let (refCompId, bytes) ← decodeUIntLE 4 bytes
  pure ({ refCompId }, bytes)

@[simp] theorem encode_length (message : CompIdsGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : CompIdsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompIdsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CompIdsGroup

/-- Comp Ids Groups -/
structure CompIdsGroups where
  blockLength : BitVec 16
  compIdsGroup : Bounded 1 CompIdsGroup
  deriving DecidableEq, Repr

namespace CompIdsGroups

def encode (message : CompIdsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.compIdsGroup.val.length)
    ++ (encodeMany CompIdsGroup.encode message.compIdsGroup.val))

def decode (bytes : List UInt8) : Option (CompIdsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (compIdsGroup_, bytes) ← decodeMany CompIdsGroup.decode numInGroup.toNat bytes
  if fits_compIdsGroup : compIdsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, compIdsGroup := ⟨compIdsGroup_, fits_compIdsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : CompIdsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CompIdsGroups) : (encode message).length ≤ 1023 := by
  have bound_compIdsGroup := message.compIdsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const CompIdsGroup.encode 4 CompIdsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : CompIdsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 CompIdsGroup.encode CompIdsGroup.decode CompIdsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.compIdsGroup.length_lt]
  rfl

end CompIdsGroups

/-- Order Mass Action Report Message -/
structure OrderMassActionReportMessage where
  outboundBusinessHeader : OutboundBusinessHeader
  massActionType : BitVec 8
  massActionScope : BitVec 8
  clordid : BitVec 64
  massActionReportId : BitVec 64
  transactTime : BitVec 64
  massActionResponse : MassActionResponse
  massActionRejectReason : BitVec 8
  massCancelRestatementReason : BitVec 8
  ordtagid : BitVec 8
  sideOptional : SideOptional
  offset49Padding1 : Alpha 1
  asset : Alpha 6
  securityIdOptional : BitVec 64
  actionTargetSessionId : BitVec 32
  actionTargetGroupId : BitVec 32
  compIdsGroups : CompIdsGroups
  text : Text
  deriving DecidableEq, Repr

namespace OrderMassActionReportMessage

def encode (message : OrderMassActionReportMessage) : List UInt8 :=
  OutboundBusinessHeader.encode message.outboundBusinessHeader
    ++ (encodeUInt 1 message.massActionType
    ++ (encodeUInt 1 message.massActionScope
    ++ (encodeUIntLE 8 message.clordid
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (MassActionResponse.encode message.massActionResponse
    ++ (encodeUInt 1 message.massActionRejectReason
    ++ (encodeUInt 1 message.massCancelRestatementReason
    ++ (encodeUInt 1 message.ordtagid
    ++ (SideOptional.encode message.sideOptional
    ++ (Alpha.encode message.offset49Padding1
    ++ (Alpha.encode message.asset
    ++ (encodeUIntLE 8 message.securityIdOptional
    ++ (encodeUIntLE 4 message.actionTargetSessionId
    ++ (encodeUIntLE 4 message.actionTargetGroupId
    ++ (CompIdsGroups.encode message.compIdsGroups
    ++ (Text.encode message.text)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderMassActionReportMessage × List UInt8) := do
  let (outboundBusinessHeader, bytes) ← OutboundBusinessHeader.decode bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionScope, bytes) ← decodeUInt 1 bytes
  let (clordid, bytes) ← decodeUIntLE 8 bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (massActionResponse, bytes) ← MassActionResponse.decode bytes
  let (massActionRejectReason, bytes) ← decodeUInt 1 bytes
  let (massCancelRestatementReason, bytes) ← decodeUInt 1 bytes
  let (ordtagid, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (offset49Padding1, bytes) ← Alpha.decode 1 bytes
  let (asset, bytes) ← Alpha.decode 6 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (actionTargetSessionId, bytes) ← decodeUIntLE 4 bytes
  let (actionTargetGroupId, bytes) ← decodeUIntLE 4 bytes
  let (compIdsGroups, bytes) ← CompIdsGroups.decode bytes
  let (text, bytes) ← Text.decode bytes
  pure ({ outboundBusinessHeader, massActionType, massActionScope, clordid, massActionReportId, transactTime, massActionResponse, massActionRejectReason, massCancelRestatementReason, ordtagid, sideOptional, offset49Padding1, asset, securityIdOptional, actionTargetSessionId, actionTargetGroupId, compIdsGroups, text }, bytes)

theorem encode_length_pos (message : OrderMassActionReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutboundBusinessHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderMassActionReportMessage) : (encode message).length ≤ 1351 := by
  have bound_compIdsGroups := CompIdsGroups.encode_length_le message.compIdsGroups
  have bound_text := Text.encode_length_le message.text
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutboundBusinessHeader.encode_length, encodeUInt_length, encodeUIntLE_length, MassActionResponse.encode_length, SideOptional.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderMassActionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutboundBusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MassActionResponse.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CompIdsGroups.decode_encode, some_bind]
  dsimp only
  rw [Text.decode_encode, some_bind]
  rfl

end OrderMassActionReportMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | negotiateMessage (message : NegotiateMessage) -- 1
  | negotiateResponseMessage (message : NegotiateResponseMessage) -- 2
  | negotiateRejectMessage (message : NegotiateRejectMessage) -- 3
  | establishMessage (message : EstablishMessage) -- 4
  | establishAckMessage (message : EstablishAckMessage) -- 5
  | establishRejectMessage (message : EstablishRejectMessage) -- 6
  | terminateMessage (message : TerminateMessage) -- 7
  | notAppliedMessage (message : NotAppliedMessage) -- 8
  | sequenceMessage (message : SequenceMessage) -- 9
  | retransmitRequestMessage (message : RetransmitRequestMessage) -- 12
  | retransmissionMessage (message : RetransmissionMessage) -- 13
  | retransmitRejectMessage (message : RetransmitRejectMessage) -- 14
  | simpleNewOrderMessage (message : SimpleNewOrderMessage) -- 100
  | simpleModifyOrderMessage (message : SimpleModifyOrderMessage) -- 101
  | newOrderSingleMessage (message : NewOrderSingleMessage) -- 102
  | orderCancelReplaceRequestMessage (message : OrderCancelReplaceRequestMessage) -- 104
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 105
  | newOrderCrossMessage (message : NewOrderCrossMessage) -- 106
  | executionReportNewMessage (message : ExecutionReportNewMessage) -- 200
  | executionReportModifyMessage (message : ExecutionReportModifyMessage) -- 201
  | executionReportCancelMessage (message : ExecutionReportCancelMessage) -- 202
  | executionReportTradeMessage (message : ExecutionReportTradeMessage) -- 203
  | executionReportRejectMessage (message : ExecutionReportRejectMessage) -- 204
  | executionReportForwardMessage (message : ExecutionReportForwardMessage) -- 205
  | businessMessageRejectMessage (message : BusinessMessageRejectMessage) -- 206
  | securityDefinitionRequestMessage (message : SecurityDefinitionRequestMessage) -- 300
  | securityDefinitionResponseMessage (message : SecurityDefinitionResponseMessage) -- 301
  | quoteRequestMessage (message : QuoteRequestMessage) -- 401
  | quoteStatusReportMessage (message : QuoteStatusReportMessage) -- 402
  | quoteMessage (message : QuoteMessage) -- 403
  | quoteCancelMessage (message : QuoteCancelMessage) -- 404
  | quoteRequestRejectMessage (message : QuoteRequestRejectMessage) -- 405
  | positionMaintenanceCancelRequestMessage (message : PositionMaintenanceCancelRequestMessage) -- 501
  | positionMaintenanceRequestMessage (message : PositionMaintenanceRequestMessage) -- 502
  | positionMaintenanceReportMessage (message : PositionMaintenanceReportMessage) -- 503
  | allocationInstructionMessage (message : AllocationInstructionMessage) -- 601
  | allocationReportMessage (message : AllocationReportMessage) -- 602
  | orderMassActionRequestMessage (message : OrderMassActionRequestMessage) -- 701
  | orderMassActionReportMessage (message : OrderMassActionReportMessage) -- 702
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .negotiateMessage _ => 1
  | .negotiateResponseMessage _ => 2
  | .negotiateRejectMessage _ => 3
  | .establishMessage _ => 4
  | .establishAckMessage _ => 5
  | .establishRejectMessage _ => 6
  | .terminateMessage _ => 7
  | .notAppliedMessage _ => 8
  | .sequenceMessage _ => 9
  | .retransmitRequestMessage _ => 12
  | .retransmissionMessage _ => 13
  | .retransmitRejectMessage _ => 14
  | .simpleNewOrderMessage _ => 100
  | .simpleModifyOrderMessage _ => 101
  | .newOrderSingleMessage _ => 102
  | .orderCancelReplaceRequestMessage _ => 104
  | .orderCancelRequestMessage _ => 105
  | .newOrderCrossMessage _ => 106
  | .executionReportNewMessage _ => 200
  | .executionReportModifyMessage _ => 201
  | .executionReportCancelMessage _ => 202
  | .executionReportTradeMessage _ => 203
  | .executionReportRejectMessage _ => 204
  | .executionReportForwardMessage _ => 205
  | .businessMessageRejectMessage _ => 206
  | .securityDefinitionRequestMessage _ => 300
  | .securityDefinitionResponseMessage _ => 301
  | .quoteRequestMessage _ => 401
  | .quoteStatusReportMessage _ => 402
  | .quoteMessage _ => 403
  | .quoteCancelMessage _ => 404
  | .quoteRequestRejectMessage _ => 405
  | .positionMaintenanceCancelRequestMessage _ => 501
  | .positionMaintenanceRequestMessage _ => 502
  | .positionMaintenanceReportMessage _ => 503
  | .allocationInstructionMessage _ => 601
  | .allocationReportMessage _ => 602
  | .orderMassActionRequestMessage _ => 701
  | .orderMassActionReportMessage _ => 702

def encode : Payload → List UInt8
  | .negotiateMessage message => NegotiateMessage.encode message
  | .negotiateResponseMessage message => NegotiateResponseMessage.encode message
  | .negotiateRejectMessage message => NegotiateRejectMessage.encode message
  | .establishMessage message => EstablishMessage.encode message
  | .establishAckMessage message => EstablishAckMessage.encode message
  | .establishRejectMessage message => EstablishRejectMessage.encode message
  | .terminateMessage message => TerminateMessage.encode message
  | .notAppliedMessage message => NotAppliedMessage.encode message
  | .sequenceMessage message => SequenceMessage.encode message
  | .retransmitRequestMessage message => RetransmitRequestMessage.encode message
  | .retransmissionMessage message => RetransmissionMessage.encode message
  | .retransmitRejectMessage message => RetransmitRejectMessage.encode message
  | .simpleNewOrderMessage message => SimpleNewOrderMessage.encode message
  | .simpleModifyOrderMessage message => SimpleModifyOrderMessage.encode message
  | .newOrderSingleMessage message => NewOrderSingleMessage.encode message
  | .orderCancelReplaceRequestMessage message => OrderCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .newOrderCrossMessage message => NewOrderCrossMessage.encode message
  | .executionReportNewMessage message => ExecutionReportNewMessage.encode message
  | .executionReportModifyMessage message => ExecutionReportModifyMessage.encode message
  | .executionReportCancelMessage message => ExecutionReportCancelMessage.encode message
  | .executionReportTradeMessage message => ExecutionReportTradeMessage.encode message
  | .executionReportRejectMessage message => ExecutionReportRejectMessage.encode message
  | .executionReportForwardMessage message => ExecutionReportForwardMessage.encode message
  | .businessMessageRejectMessage message => BusinessMessageRejectMessage.encode message
  | .securityDefinitionRequestMessage message => SecurityDefinitionRequestMessage.encode message
  | .securityDefinitionResponseMessage message => SecurityDefinitionResponseMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .quoteStatusReportMessage message => QuoteStatusReportMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message
  | .quoteCancelMessage message => QuoteCancelMessage.encode message
  | .quoteRequestRejectMessage message => QuoteRequestRejectMessage.encode message
  | .positionMaintenanceCancelRequestMessage message => PositionMaintenanceCancelRequestMessage.encode message
  | .positionMaintenanceRequestMessage message => PositionMaintenanceRequestMessage.encode message
  | .positionMaintenanceReportMessage message => PositionMaintenanceReportMessage.encode message
  | .allocationInstructionMessage message => AllocationInstructionMessage.encode message
  | .allocationReportMessage message => AllocationReportMessage.encode message
  | .orderMassActionRequestMessage message => OrderMassActionRequestMessage.encode message
  | .orderMassActionReportMessage message => OrderMassActionReportMessage.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (NegotiateMessage.decode bytes).map fun (message, rest) => (.negotiateMessage message, rest)
  else if tag = 2 then (NegotiateResponseMessage.decode bytes).map fun (message, rest) => (.negotiateResponseMessage message, rest)
  else if tag = 3 then (NegotiateRejectMessage.decode bytes).map fun (message, rest) => (.negotiateRejectMessage message, rest)
  else if tag = 4 then (EstablishMessage.decode bytes).map fun (message, rest) => (.establishMessage message, rest)
  else if tag = 5 then (EstablishAckMessage.decode bytes).map fun (message, rest) => (.establishAckMessage message, rest)
  else if tag = 6 then (EstablishRejectMessage.decode bytes).map fun (message, rest) => (.establishRejectMessage message, rest)
  else if tag = 7 then (TerminateMessage.decode bytes).map fun (message, rest) => (.terminateMessage message, rest)
  else if tag = 8 then (NotAppliedMessage.decode bytes).map fun (message, rest) => (.notAppliedMessage message, rest)
  else if tag = 9 then (SequenceMessage.decode bytes).map fun (message, rest) => (.sequenceMessage message, rest)
  else if tag = 12 then (RetransmitRequestMessage.decode bytes).map fun (message, rest) => (.retransmitRequestMessage message, rest)
  else if tag = 13 then (RetransmissionMessage.decode bytes).map fun (message, rest) => (.retransmissionMessage message, rest)
  else if tag = 14 then (RetransmitRejectMessage.decode bytes).map fun (message, rest) => (.retransmitRejectMessage message, rest)
  else if tag = 100 then (SimpleNewOrderMessage.decode bytes).map fun (message, rest) => (.simpleNewOrderMessage message, rest)
  else if tag = 101 then (SimpleModifyOrderMessage.decode bytes).map fun (message, rest) => (.simpleModifyOrderMessage message, rest)
  else if tag = 102 then (NewOrderSingleMessage.decode bytes).map fun (message, rest) => (.newOrderSingleMessage message, rest)
  else if tag = 104 then (OrderCancelReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequestMessage message, rest)
  else if tag = 105 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 106 then (NewOrderCrossMessage.decode bytes).map fun (message, rest) => (.newOrderCrossMessage message, rest)
  else if tag = 200 then (ExecutionReportNewMessage.decode bytes).map fun (message, rest) => (.executionReportNewMessage message, rest)
  else if tag = 201 then (ExecutionReportModifyMessage.decode bytes).map fun (message, rest) => (.executionReportModifyMessage message, rest)
  else if tag = 202 then (ExecutionReportCancelMessage.decode bytes).map fun (message, rest) => (.executionReportCancelMessage message, rest)
  else if tag = 203 then (ExecutionReportTradeMessage.decode bytes).map fun (message, rest) => (.executionReportTradeMessage message, rest)
  else if tag = 204 then (ExecutionReportRejectMessage.decode bytes).map fun (message, rest) => (.executionReportRejectMessage message, rest)
  else if tag = 205 then (ExecutionReportForwardMessage.decode bytes).map fun (message, rest) => (.executionReportForwardMessage message, rest)
  else if tag = 206 then (BusinessMessageRejectMessage.decode bytes).map fun (message, rest) => (.businessMessageRejectMessage message, rest)
  else if tag = 300 then (SecurityDefinitionRequestMessage.decode bytes).map fun (message, rest) => (.securityDefinitionRequestMessage message, rest)
  else if tag = 301 then (SecurityDefinitionResponseMessage.decode bytes).map fun (message, rest) => (.securityDefinitionResponseMessage message, rest)
  else if tag = 401 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 402 then (QuoteStatusReportMessage.decode bytes).map fun (message, rest) => (.quoteStatusReportMessage message, rest)
  else if tag = 403 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 404 then (QuoteCancelMessage.decode bytes).map fun (message, rest) => (.quoteCancelMessage message, rest)
  else if tag = 405 then (QuoteRequestRejectMessage.decode bytes).map fun (message, rest) => (.quoteRequestRejectMessage message, rest)
  else if tag = 501 then (PositionMaintenanceCancelRequestMessage.decode bytes).map fun (message, rest) => (.positionMaintenanceCancelRequestMessage message, rest)
  else if tag = 502 then (PositionMaintenanceRequestMessage.decode bytes).map fun (message, rest) => (.positionMaintenanceRequestMessage message, rest)
  else if tag = 503 then (PositionMaintenanceReportMessage.decode bytes).map fun (message, rest) => (.positionMaintenanceReportMessage message, rest)
  else if tag = 601 then (AllocationInstructionMessage.decode bytes).map fun (message, rest) => (.allocationInstructionMessage message, rest)
  else if tag = 602 then (AllocationReportMessage.decode bytes).map fun (message, rest) => (.allocationReportMessage message, rest)
  else if tag = 701 then (OrderMassActionRequestMessage.decode bytes).map fun (message, rest) => (.orderMassActionRequestMessage message, rest)
  else if tag = 702 then (OrderMassActionReportMessage.decode bytes).map fun (message, rest) => (.orderMassActionReportMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Simple Open Frame -/
structure SimpleOpenFrame where
  encodingType : BitVec 16
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SimpleOpenFrame

def encodeBody (message : SimpleOpenFrame) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ (encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload)))))

def decodeBody (bytes : List UInt8) : Option (SimpleOpenFrame × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ encodingType, blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : SimpleOpenFrame) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SimpleOpenFrame) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | negotiateMessage inner =>
    have bound_inner := NegotiateMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | negotiateResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NegotiateResponseMessage.encode_length]
    omega
  | negotiateRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NegotiateRejectMessage.encode_length]
    omega
  | establishMessage inner =>
    have bound_inner := EstablishMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | establishAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EstablishAckMessage.encode_length]
    omega
  | establishRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EstablishRejectMessage.encode_length]
    omega
  | terminateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TerminateMessage.encode_length]
    omega
  | notAppliedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NotAppliedMessage.encode_length]
    omega
  | sequenceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceMessage.encode_length]
    omega
  | retransmitRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmitRequestMessage.encode_length]
    omega
  | retransmissionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmissionMessage.encode_length]
    omega
  | retransmitRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmitRejectMessage.encode_length]
    omega
  | simpleNewOrderMessage inner =>
    have bound_inner := SimpleNewOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | simpleModifyOrderMessage inner =>
    have bound_inner := SimpleModifyOrderMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | newOrderSingleMessage inner =>
    have bound_inner := NewOrderSingleMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | orderCancelReplaceRequestMessage inner =>
    have bound_inner := OrderCancelReplaceRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | orderCancelRequestMessage inner =>
    have bound_inner := OrderCancelRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | newOrderCrossMessage inner =>
    have bound_inner := NewOrderCrossMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportNewMessage inner =>
    have bound_inner := ExecutionReportNewMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportModifyMessage inner =>
    have bound_inner := ExecutionReportModifyMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportCancelMessage inner =>
    have bound_inner := ExecutionReportCancelMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportTradeMessage inner =>
    have bound_inner := ExecutionReportTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportRejectMessage inner =>
    have bound_inner := ExecutionReportRejectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | executionReportForwardMessage inner =>
    have bound_inner := ExecutionReportForwardMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | businessMessageRejectMessage inner =>
    have bound_inner := BusinessMessageRejectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityDefinitionRequestMessage inner =>
    have bound_inner := SecurityDefinitionRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityDefinitionResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityDefinitionResponseMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    have bound_inner := QuoteRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteStatusReportMessage inner =>
    have bound_inner := QuoteStatusReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteCancelMessage inner =>
    have bound_inner := QuoteCancelMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | quoteRequestRejectMessage inner =>
    have bound_inner := QuoteRequestRejectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | positionMaintenanceCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PositionMaintenanceCancelRequestMessage.encode_length]
    omega
  | positionMaintenanceRequestMessage inner =>
    have bound_inner := PositionMaintenanceRequestMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | positionMaintenanceReportMessage inner =>
    have bound_inner := PositionMaintenanceReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | allocationInstructionMessage inner =>
    have bound_inner := AllocationInstructionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | allocationReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AllocationReportMessage.encode_length]
    omega
  | orderMassActionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassActionRequestMessage.encode_length]
    omega
  | orderMassActionReportMessage inner =>
    have bound_inner := OrderMassActionReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : SimpleOpenFrame → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (SimpleOpenFrame × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : SimpleOpenFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SimpleOpenFrame) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SimpleOpenFrame

/-- Packet -/
structure Packet where
  simpleOpenFrame : List SimpleOpenFrame
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SimpleOpenFrame.encode message.simpleOpenFrame

def decode (bytes : List UInt8) : Option Packet := do
  let simpleOpenFrame ← decodeAll SimpleOpenFrame.decode bytes.length bytes
  pure { simpleOpenFrame }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SimpleOpenFrame.encode SimpleOpenFrame.decode SimpleOpenFrame.decode_encode SimpleOpenFrame.encode_length_pos message.simpleOpenFrame _ (encodeMany_length_ge SimpleOpenFrame.encode SimpleOpenFrame.encode_length_pos message.simpleOpenFrame), some_bind]
  rfl

end Packet

end Omi.B3B3derivativesBinaryentrypointSbeV70
