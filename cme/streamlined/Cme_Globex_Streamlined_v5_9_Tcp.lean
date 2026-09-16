import Omi.Wire

/-!
# CME Group Streamlined Market Data v5.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Settl Price Type is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Message's Tcp Message Size is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexStreamlinedSbeV59Tcp

/-- Security Update Action: one byte code -/
inductive SecurityUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  deriving DecidableEq, Repr

namespace SecurityUpdateAction

def toByte : SecurityUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D

def ofByte? (byte : UInt8) : Option SecurityUpdateAction :=
  if byte = 0x41 then some .add
  else if byte = 0x44 then some .delete
  else if byte = 0x4D then some .modify
  else none

theorem ofByte?_toByte (value : SecurityUpdateAction) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : SecurityUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityUpdateAction × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end SecurityUpdateAction

/-- Md Entry Type Indices: one byte code -/
inductive MdEntryTypeIndices where
  | bid -- Bid
  | offer -- Offer
  | trade -- Trade
  | indexValue -- Index Value
  | openingValue -- Opening Value
  | closingPrice -- Closing Price
  | settlementPrice -- Settlement Price
  | sessionHighPrice -- Session High Price
  | sessionLowPrice -- Session Low Price
  | tradeVolume -- Trade Volume
  deriving DecidableEq, Repr

namespace MdEntryTypeIndices

def toByte : MdEntryTypeIndices → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .indexValue => 0x33
  | .openingValue => 0x34
  | .closingPrice => 0x35
  | .settlementPrice => 0x36
  | .sessionHighPrice => 0x37
  | .sessionLowPrice => 0x38
  | .tradeVolume => 0x65

def ofByte? (byte : UInt8) : Option MdEntryTypeIndices :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x32 then some .trade
  else if byte = 0x33 then some .indexValue
  else if byte = 0x34 then some .openingValue
  else if byte = 0x35 then some .closingPrice
  else if byte = 0x36 then some .settlementPrice
  else if byte = 0x37 then some .sessionHighPrice
  else if byte = 0x38 then some .sessionLowPrice
  else if byte = 0x65 then some .tradeVolume
  else none

theorem ofByte?_toByte (value : MdEntryTypeIndices) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeIndices) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeIndices × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeIndices) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeIndices) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeIndices

/-- Technical Header: 14 bytes -/
structure TechnicalHeader where
  encodingType : BitVec 16
  messageSequenceNumber : BitVec 32
  tcpSendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace TechnicalHeader

def encode (message : TechnicalHeader) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 4 message.messageSequenceNumber
    ++ encodeUIntLE 8 message.tcpSendingTime

def decode (bytes : List UInt8) : Option (TechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : TechnicalHeader) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TechnicalHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end TechnicalHeader

/-- Admin Heartbeat: 0 bytes -/
structure AdminHeartbeat where
  deriving DecidableEq, Repr

namespace AdminHeartbeat

def encode (_ : AdminHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AdminHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AdminHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AdminHeartbeat

/-- Admin Login: 1 bytes -/
structure AdminLogin where
  heartBtInt : BitVec 8
  deriving DecidableEq, Repr

namespace AdminLogin

def encode (message : AdminLogin) : List UInt8 :=
  encodeUInt 1 message.heartBtInt

def decode (bytes : List UInt8) : Option (AdminLogin × List UInt8) := do
  let (heartBtInt, bytes) ← decodeUInt 1 bytes
  pure ({ heartBtInt }, bytes)

@[simp] theorem encode_length (message : AdminLogin) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : AdminLogin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end AdminLogin

/-- Admin Logout: 180 bytes -/
structure AdminLogout where
  text : Alpha 180
  deriving DecidableEq, Repr

namespace AdminLogout

def encode (message : AdminLogout) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (AdminLogout × List UInt8) := do
  let (text, bytes) ← Alpha.decode 180 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : AdminLogout) : (encode message).length = 180 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : AdminLogout) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminLogout) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AdminLogout

/-- Md Entry Px Decimal Optional: 9 bytes -/
structure MdEntryPxDecimalOptional where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MdEntryPxDecimalOptional

def encode (message : MdEntryPxDecimalOptional) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MdEntryPxDecimalOptional × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MdEntryPxDecimalOptional) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MdEntryPxDecimalOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdEntryPxDecimalOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MdEntryPxDecimalOptional

/-- Cal Fut Px Optional: 9 bytes -/
structure CalFutPxOptional where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace CalFutPxOptional

def encode (message : CalFutPxOptional) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (CalFutPxOptional × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : CalFutPxOptional) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CalFutPxOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CalFutPxOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end CalFutPxOptional

/-- Coupon Rate Optional: 5 bytes -/
structure CouponRateOptional where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace CouponRateOptional

def encode (message : CouponRateOptional) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (CouponRateOptional × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : CouponRateOptional) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CouponRateOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CouponRateOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end CouponRateOptional

/-- Fair Coupon Pct: 9 bytes -/
structure FairCouponPct where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FairCouponPct

def encode (message : FairCouponPct) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FairCouponPct × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FairCouponPct) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FairCouponPct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FairCouponPct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FairCouponPct

/-- Leg Purchase Rate: 9 bytes -/
structure LegPurchaseRate where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LegPurchaseRate

def encode (message : LegPurchaseRate) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LegPurchaseRate × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : LegPurchaseRate) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegPurchaseRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegPurchaseRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegPurchaseRate

/-- Fixed Npv: 9 bytes -/
structure FixedNpv where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FixedNpv

def encode (message : FixedNpv) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FixedNpv × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FixedNpv) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FixedNpv) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FixedNpv) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FixedNpv

/-- Float Npv: 9 bytes -/
structure FloatNpv where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FloatNpv

def encode (message : FloatNpv) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FloatNpv × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FloatNpv) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FloatNpv) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FloatNpv) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FloatNpv

/-- Npv: 9 bytes -/
structure Npv where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace Npv

def encode (message : Npv) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (Npv × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : Npv) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Npv) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Npv) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Npv

/-- Accrued Coupons: 9 bytes -/
structure AccruedCoupons where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace AccruedCoupons

def encode (message : AccruedCoupons) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (AccruedCoupons × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : AccruedCoupons) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AccruedCoupons) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccruedCoupons) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end AccruedCoupons

/-- Daily Incremental Eris Pai: 9 bytes -/
structure DailyIncrementalErisPai where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace DailyIncrementalErisPai

def encode (message : DailyIncrementalErisPai) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (DailyIncrementalErisPai × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : DailyIncrementalErisPai) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DailyIncrementalErisPai) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DailyIncrementalErisPai) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end DailyIncrementalErisPai

/-- Eris Pai: 9 bytes -/
structure ErisPai where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace ErisPai

def encode (message : ErisPai) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (ErisPai × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : ErisPai) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ErisPai) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErisPai) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ErisPai

/-- Fed Funds Rate: 9 bytes -/
structure FedFundsRate where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FedFundsRate

def encode (message : FedFundsRate) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FedFundsRate × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FedFundsRate) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FedFundsRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FedFundsRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FedFundsRate

/-- Min Price Increment Optional: 9 bytes -/
structure MinPriceIncrementOptional where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MinPriceIncrementOptional

def encode (message : MinPriceIncrementOptional) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MinPriceIncrementOptional × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MinPriceIncrementOptional) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MinPriceIncrementOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinPriceIncrementOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MinPriceIncrementOptional

/-- Fixed Payment: 9 bytes -/
structure FixedPayment where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FixedPayment

def encode (message : FixedPayment) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FixedPayment × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FixedPayment) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FixedPayment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FixedPayment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FixedPayment

/-- Floating Payment: 9 bytes -/
structure FloatingPayment where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FloatingPayment

def encode (message : FloatingPayment) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FloatingPayment × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FloatingPayment) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FloatingPayment) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FloatingPayment) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FloatingPayment

/-- Next Fixed Payment Amount: 9 bytes -/
structure NextFixedPaymentAmount where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace NextFixedPaymentAmount

def encode (message : NextFixedPaymentAmount) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (NextFixedPaymentAmount × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : NextFixedPaymentAmount) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NextFixedPaymentAmount) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextFixedPaymentAmount) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NextFixedPaymentAmount

/-- Next Floating Payment Amount: 9 bytes -/
structure NextFloatingPaymentAmount where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace NextFloatingPaymentAmount

def encode (message : NextFloatingPaymentAmount) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (NextFloatingPaymentAmount × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : NextFloatingPaymentAmount) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NextFloatingPaymentAmount) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NextFloatingPaymentAmount) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NextFloatingPaymentAmount

/-- Previous Eris Pai: 9 bytes -/
structure PreviousErisPai where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousErisPai

def encode (message : PreviousErisPai) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (PreviousErisPai × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : PreviousErisPai) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousErisPai) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousErisPai) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end PreviousErisPai

/-- Leg Contract Multiplier: 9 bytes -/
structure LegContractMultiplier where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LegContractMultiplier

def encode (message : LegContractMultiplier) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LegContractMultiplier × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : LegContractMultiplier) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegContractMultiplier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegContractMultiplier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegContractMultiplier

/-- P V 01: 9 bytes -/
structure PV01 where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace PV01

def encode (message : PV01) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (PV01 × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : PV01) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PV01) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PV01) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end PV01

/-- D V 01: 9 bytes -/
structure DV01 where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace DV01

def encode (message : DV01) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (DV01 × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : DV01) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DV01) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DV01) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end DV01

/-- Settlement Npv: 9 bytes -/
structure SettlementNpv where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementNpv

def encode (message : SettlementNpv) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (SettlementNpv × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : SettlementNpv) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementNpv) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementNpv) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SettlementNpv

/-- Final Settlement Futures Price: 9 bytes -/
structure FinalSettlementFuturesPrice where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FinalSettlementFuturesPrice

def encode (message : FinalSettlementFuturesPrice) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FinalSettlementFuturesPrice × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FinalSettlementFuturesPrice) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FinalSettlementFuturesPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinalSettlementFuturesPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FinalSettlementFuturesPrice

/-- Eris Security Alt Id Group: 27 bytes -/
structure ErisSecurityAltIdGroup where
  securityAltId50 : Alpha 26
  securityAltIdSourceOptional : Alpha 1
  deriving DecidableEq, Repr

namespace ErisSecurityAltIdGroup

def encode (message : ErisSecurityAltIdGroup) : List UInt8 :=
  Alpha.encode message.securityAltId50
    ++ Alpha.encode message.securityAltIdSourceOptional

def decode (bytes : List UInt8) : Option (ErisSecurityAltIdGroup × List UInt8) := do
  let (securityAltId50, bytes) ← Alpha.decode 26 bytes
  let (securityAltIdSourceOptional, bytes) ← Alpha.decode 1 bytes
  pure ({ securityAltId50, securityAltIdSourceOptional }, bytes)

@[simp] theorem encode_length (message : ErisSecurityAltIdGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErisSecurityAltIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErisSecurityAltIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ErisSecurityAltIdGroup

/-- Eris Security Alt Id Groups -/
structure ErisSecurityAltIdGroups where
  blockLength : BitVec 16
  erisSecurityAltIdGroup : Bounded 1 ErisSecurityAltIdGroup
  deriving DecidableEq, Repr

namespace ErisSecurityAltIdGroups

def encode (message : ErisSecurityAltIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisSecurityAltIdGroup.val.length)
    ++ encodeMany ErisSecurityAltIdGroup.encode message.erisSecurityAltIdGroup.val

def decode (bytes : List UInt8) : Option (ErisSecurityAltIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisSecurityAltIdGroup_, bytes) ← decodeMany ErisSecurityAltIdGroup.decode numInGroup8.toNat bytes
  if fits_erisSecurityAltIdGroup : erisSecurityAltIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisSecurityAltIdGroup := ⟨erisSecurityAltIdGroup_, fits_erisSecurityAltIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisSecurityAltIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisSecurityAltIdGroups) : (encode message).length ≤ 6888 := by
  have bound_erisSecurityAltIdGroup := message.erisSecurityAltIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const ErisSecurityAltIdGroup.encode 27 ErisSecurityAltIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ErisSecurityAltIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisSecurityAltIdGroup.encode ErisSecurityAltIdGroup.decode ErisSecurityAltIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisSecurityAltIdGroup.length_lt, ↓reduceDIte]
  rfl

end ErisSecurityAltIdGroups

/-- Incremental Refresh Eris Related Instruments Group: 77 bytes -/
structure IncrementalRefreshErisRelatedInstrumentsGroup where
  relatedInstrumentType : BitVec 8
  relatedSymbol : Alpha 50
  relatedSecurityGroup : Alpha 26
  deriving DecidableEq, Repr

namespace IncrementalRefreshErisRelatedInstrumentsGroup

def encode (message : IncrementalRefreshErisRelatedInstrumentsGroup) : List UInt8 :=
  encodeUInt 1 message.relatedInstrumentType
    ++ Alpha.encode message.relatedSymbol
    ++ Alpha.encode message.relatedSecurityGroup

def decode (bytes : List UInt8) : Option (IncrementalRefreshErisRelatedInstrumentsGroup × List UInt8) := do
  let (relatedInstrumentType, bytes) ← decodeUInt 1 bytes
  let (relatedSymbol, bytes) ← Alpha.decode 50 bytes
  let (relatedSecurityGroup, bytes) ← Alpha.decode 26 bytes
  pure ({ relatedInstrumentType, relatedSymbol, relatedSecurityGroup }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshErisRelatedInstrumentsGroup) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IncrementalRefreshErisRelatedInstrumentsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshErisRelatedInstrumentsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshErisRelatedInstrumentsGroup

/-- Incremental Refresh Eris Related Instruments Groups -/
structure IncrementalRefreshErisRelatedInstrumentsGroups where
  blockLength : BitVec 16
  incrementalRefreshErisRelatedInstrumentsGroup : Bounded 1 IncrementalRefreshErisRelatedInstrumentsGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshErisRelatedInstrumentsGroups

def encode (message : IncrementalRefreshErisRelatedInstrumentsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshErisRelatedInstrumentsGroup.val.length)
    ++ encodeMany IncrementalRefreshErisRelatedInstrumentsGroup.encode message.incrementalRefreshErisRelatedInstrumentsGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshErisRelatedInstrumentsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshErisRelatedInstrumentsGroup_, bytes) ← decodeMany IncrementalRefreshErisRelatedInstrumentsGroup.decode numInGroup8.toNat bytes
  if fits_incrementalRefreshErisRelatedInstrumentsGroup : incrementalRefreshErisRelatedInstrumentsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshErisRelatedInstrumentsGroup := ⟨incrementalRefreshErisRelatedInstrumentsGroup_, fits_incrementalRefreshErisRelatedInstrumentsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshErisRelatedInstrumentsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshErisRelatedInstrumentsGroups) : (encode message).length ≤ 19638 := by
  have bound_incrementalRefreshErisRelatedInstrumentsGroup := message.incrementalRefreshErisRelatedInstrumentsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshErisRelatedInstrumentsGroup.encode 77 IncrementalRefreshErisRelatedInstrumentsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshErisRelatedInstrumentsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshErisRelatedInstrumentsGroup.encode IncrementalRefreshErisRelatedInstrumentsGroup.decode IncrementalRefreshErisRelatedInstrumentsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshErisRelatedInstrumentsGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshErisRelatedInstrumentsGroups

/-- Events Group: 9 bytes -/
structure EventsGroup where
  eventTypeOptional : BitVec 8
  eventTimeOptional : BitVec 64
  deriving DecidableEq, Repr

namespace EventsGroup

def encode (message : EventsGroup) : List UInt8 :=
  encodeUInt 1 message.eventTypeOptional
    ++ encodeUIntLE 8 message.eventTimeOptional

def decode (bytes : List UInt8) : Option (EventsGroup × List UInt8) := do
  let (eventTypeOptional, bytes) ← decodeUInt 1 bytes
  let (eventTimeOptional, bytes) ← decodeUIntLE 8 bytes
  pure ({ eventTypeOptional, eventTimeOptional }, bytes)

@[simp] theorem encode_length (message : EventsGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : EventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end EventsGroup

/-- Events Groups -/
structure EventsGroups where
  blockLength : BitVec 16
  eventsGroup : Bounded 1 EventsGroup
  deriving DecidableEq, Repr

namespace EventsGroups

def encode (message : EventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.eventsGroup.val.length)
    ++ encodeMany EventsGroup.encode message.eventsGroup.val

def decode (bytes : List UInt8) : Option (EventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (eventsGroup_, bytes) ← decodeMany EventsGroup.decode numInGroup8.toNat bytes
  if fits_eventsGroup : eventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, eventsGroup := ⟨eventsGroup_, fits_eventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : EventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EventsGroups) : (encode message).length ≤ 2298 := by
  have bound_eventsGroup := message.eventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const EventsGroup.encode 9 EventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : EventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 EventsGroup.encode EventsGroup.decode EventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.eventsGroup.length_lt, ↓reduceDIte]
  rfl

end EventsGroups

/-- Eris Reference Data Group -/
structure ErisReferenceDataGroup where
  mdUpdateActionChar : Alpha 1
  mdEntryType : Alpha 1
  rptSeq : BitVec 32
  mdEntryPxDecimalOptional : MdEntryPxDecimalOptional
  openCloseSettlFlag : BitVec 8
  settlPriceType : BitVec 8
  calFutPxOptional : CalFutPxOptional
  referenceId50 : Alpha 50
  mdEntrySizeOptional : BitVec 64
  symbol : Alpha 50
  securityGroup26 : Alpha 26
  productOptional : BitVec 8
  securityType : Alpha 9
  securityExchange : Alpha 4
  maturityDate : BitVec 16
  couponRateOptional : CouponRateOptional
  tradeDate : BitVec 16
  fairCouponPct : FairCouponPct
  legPurchaseRate : LegPurchaseRate
  fixedNpv : FixedNpv
  floatNpv : FloatNpv
  npv : Npv
  accruedCoupons : AccruedCoupons
  dailyIncrementalErisPai : DailyIncrementalErisPai
  erisPai : ErisPai
  fedFundsRate : FedFundsRate
  minPriceIncrementOptional : MinPriceIncrementOptional
  fixedPayment : FixedPayment
  floatingPayment : FloatingPayment
  nextFixedPaymentDate : BitVec 16
  nextFixedPaymentAmount : NextFixedPaymentAmount
  nextFloatingPaymentAmount : NextFloatingPaymentAmount
  tradingReferenceDate : BitVec 16
  previousErisPai : PreviousErisPai
  fedFundsDate : BitVec 16
  accrualDays : BitVec 32
  nominal : BitVec 64
  legCreditRating : Alpha 6
  legContractMultiplier : LegContractMultiplier
  nextFloatingPaymentDate : BitVec 16
  pV01 : PV01
  dV01 : DV01
  settlementNpv : SettlementNpv
  finalSettlementFuturesPrice : FinalSettlementFuturesPrice
  securityDescription : Alpha 30
  erisSecurityAltIdGroups : ErisSecurityAltIdGroups
  incrementalRefreshErisRelatedInstrumentsGroups : IncrementalRefreshErisRelatedInstrumentsGroups
  eventsGroups : EventsGroups
  deriving DecidableEq, Repr

namespace ErisReferenceDataGroup

def encode (message : ErisReferenceDataGroup) : List UInt8 :=
  Alpha.encode message.mdUpdateActionChar
    ++ Alpha.encode message.mdEntryType
    ++ encodeUIntLE 4 message.rptSeq
    ++ MdEntryPxDecimalOptional.encode message.mdEntryPxDecimalOptional
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 1 message.settlPriceType
    ++ CalFutPxOptional.encode message.calFutPxOptional
    ++ Alpha.encode message.referenceId50
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup26
    ++ encodeUInt 1 message.productOptional
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ encodeUIntLE 2 message.maturityDate
    ++ CouponRateOptional.encode message.couponRateOptional
    ++ encodeUIntLE 2 message.tradeDate
    ++ FairCouponPct.encode message.fairCouponPct
    ++ LegPurchaseRate.encode message.legPurchaseRate
    ++ FixedNpv.encode message.fixedNpv
    ++ FloatNpv.encode message.floatNpv
    ++ Npv.encode message.npv
    ++ AccruedCoupons.encode message.accruedCoupons
    ++ DailyIncrementalErisPai.encode message.dailyIncrementalErisPai
    ++ ErisPai.encode message.erisPai
    ++ FedFundsRate.encode message.fedFundsRate
    ++ MinPriceIncrementOptional.encode message.minPriceIncrementOptional
    ++ FixedPayment.encode message.fixedPayment
    ++ FloatingPayment.encode message.floatingPayment
    ++ encodeUIntLE 2 message.nextFixedPaymentDate
    ++ NextFixedPaymentAmount.encode message.nextFixedPaymentAmount
    ++ NextFloatingPaymentAmount.encode message.nextFloatingPaymentAmount
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ PreviousErisPai.encode message.previousErisPai
    ++ encodeUIntLE 2 message.fedFundsDate
    ++ encodeUIntLE 4 message.accrualDays
    ++ encodeUIntLE 8 message.nominal
    ++ Alpha.encode message.legCreditRating
    ++ LegContractMultiplier.encode message.legContractMultiplier
    ++ encodeUIntLE 2 message.nextFloatingPaymentDate
    ++ PV01.encode message.pV01
    ++ DV01.encode message.dV01
    ++ SettlementNpv.encode message.settlementNpv
    ++ FinalSettlementFuturesPrice.encode message.finalSettlementFuturesPrice
    ++ Alpha.encode message.securityDescription
    ++ ErisSecurityAltIdGroups.encode message.erisSecurityAltIdGroups
    ++ IncrementalRefreshErisRelatedInstrumentsGroups.encode message.incrementalRefreshErisRelatedInstrumentsGroups
    ++ EventsGroups.encode message.eventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ErisReferenceDataGroup × List UInt8) := do
  let (mdUpdateActionChar, bytes) ← Alpha.decode 1 bytes
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxDecimalOptional, bytes) ← MdEntryPxDecimalOptional.decode bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (calFutPxOptional, bytes) ← CalFutPxOptional.decode bytes
  let (referenceId50, bytes) ← Alpha.decode 50 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup26, bytes) ← Alpha.decode 26 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (couponRateOptional, bytes) ← CouponRateOptional.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (fairCouponPct, bytes) ← FairCouponPct.decode bytes
  let (legPurchaseRate, bytes) ← LegPurchaseRate.decode bytes
  let (fixedNpv, bytes) ← FixedNpv.decode bytes
  let (floatNpv, bytes) ← FloatNpv.decode bytes
  let (npv, bytes) ← Npv.decode bytes
  let (accruedCoupons, bytes) ← AccruedCoupons.decode bytes
  let (dailyIncrementalErisPai, bytes) ← DailyIncrementalErisPai.decode bytes
  let (erisPai, bytes) ← ErisPai.decode bytes
  let (fedFundsRate, bytes) ← FedFundsRate.decode bytes
  let (minPriceIncrementOptional, bytes) ← MinPriceIncrementOptional.decode bytes
  let (fixedPayment, bytes) ← FixedPayment.decode bytes
  let (floatingPayment, bytes) ← FloatingPayment.decode bytes
  let (nextFixedPaymentDate, bytes) ← decodeUIntLE 2 bytes
  let (nextFixedPaymentAmount, bytes) ← NextFixedPaymentAmount.decode bytes
  let (nextFloatingPaymentAmount, bytes) ← NextFloatingPaymentAmount.decode bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (previousErisPai, bytes) ← PreviousErisPai.decode bytes
  let (fedFundsDate, bytes) ← decodeUIntLE 2 bytes
  let (accrualDays, bytes) ← decodeUIntLE 4 bytes
  let (nominal, bytes) ← decodeUIntLE 8 bytes
  let (legCreditRating, bytes) ← Alpha.decode 6 bytes
  let (legContractMultiplier, bytes) ← LegContractMultiplier.decode bytes
  let (nextFloatingPaymentDate, bytes) ← decodeUIntLE 2 bytes
  let (pV01, bytes) ← PV01.decode bytes
  let (dV01, bytes) ← DV01.decode bytes
  let (settlementNpv, bytes) ← SettlementNpv.decode bytes
  let (finalSettlementFuturesPrice, bytes) ← FinalSettlementFuturesPrice.decode bytes
  let (securityDescription, bytes) ← Alpha.decode 30 bytes
  let (erisSecurityAltIdGroups, bytes) ← ErisSecurityAltIdGroups.decode bytes
  let (incrementalRefreshErisRelatedInstrumentsGroups, bytes) ← IncrementalRefreshErisRelatedInstrumentsGroups.decode bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  pure ({ mdUpdateActionChar, mdEntryType, rptSeq, mdEntryPxDecimalOptional, openCloseSettlFlag, settlPriceType, calFutPxOptional, referenceId50, mdEntrySizeOptional, symbol, securityGroup26, productOptional, securityType, securityExchange, maturityDate, couponRateOptional, tradeDate, fairCouponPct, legPurchaseRate, fixedNpv, floatNpv, npv, accruedCoupons, dailyIncrementalErisPai, erisPai, fedFundsRate, minPriceIncrementOptional, fixedPayment, floatingPayment, nextFixedPaymentDate, nextFixedPaymentAmount, nextFloatingPaymentAmount, tradingReferenceDate, previousErisPai, fedFundsDate, accrualDays, nominal, legCreditRating, legContractMultiplier, nextFloatingPaymentDate, pV01, dV01, settlementNpv, finalSettlementFuturesPrice, securityDescription, erisSecurityAltIdGroups, incrementalRefreshErisRelatedInstrumentsGroups, eventsGroups }, bytes)

theorem encode_length_pos (message : ErisReferenceDataGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisReferenceDataGroup) : (encode message).length ≤ 29243 := by
  have bound_erisSecurityAltIdGroups := ErisSecurityAltIdGroups.encode_length_le message.erisSecurityAltIdGroups
  have bound_incrementalRefreshErisRelatedInstrumentsGroups := IncrementalRefreshErisRelatedInstrumentsGroups.encode_length_le message.incrementalRefreshErisRelatedInstrumentsGroups
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, MdEntryPxDecimalOptional.encode_length, encodeUInt_length, CalFutPxOptional.encode_length, CouponRateOptional.encode_length, FairCouponPct.encode_length, LegPurchaseRate.encode_length, FixedNpv.encode_length, FloatNpv.encode_length, Npv.encode_length, AccruedCoupons.encode_length, DailyIncrementalErisPai.encode_length, ErisPai.encode_length, FedFundsRate.encode_length, MinPriceIncrementOptional.encode_length, FixedPayment.encode_length, FloatingPayment.encode_length, NextFixedPaymentAmount.encode_length, NextFloatingPaymentAmount.encode_length, PreviousErisPai.encode_length, LegContractMultiplier.encode_length, PV01.encode_length, DV01.encode_length, SettlementNpv.encode_length, FinalSettlementFuturesPrice.encode_length]
  omega

@[simp] theorem decode_encode (message : ErisReferenceDataGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryPxDecimalOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [CalFutPxOptional.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [CouponRateOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [FairCouponPct.decode_encode]
  simp only [Option.bind_some]
  rw [LegPurchaseRate.decode_encode]
  simp only [Option.bind_some]
  rw [FixedNpv.decode_encode]
  simp only [Option.bind_some]
  rw [FloatNpv.decode_encode]
  simp only [Option.bind_some]
  rw [Npv.decode_encode]
  simp only [Option.bind_some]
  rw [AccruedCoupons.decode_encode]
  simp only [Option.bind_some]
  rw [DailyIncrementalErisPai.decode_encode]
  simp only [Option.bind_some]
  rw [ErisPai.decode_encode]
  simp only [Option.bind_some]
  rw [FedFundsRate.decode_encode]
  simp only [Option.bind_some]
  rw [MinPriceIncrementOptional.decode_encode]
  simp only [Option.bind_some]
  rw [FixedPayment.decode_encode]
  simp only [Option.bind_some]
  rw [FloatingPayment.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [NextFixedPaymentAmount.decode_encode]
  simp only [Option.bind_some]
  rw [NextFloatingPaymentAmount.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [PreviousErisPai.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [LegContractMultiplier.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [PV01.decode_encode]
  simp only [Option.bind_some]
  rw [DV01.decode_encode]
  simp only [Option.bind_some]
  rw [SettlementNpv.decode_encode]
  simp only [Option.bind_some]
  rw [FinalSettlementFuturesPrice.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ErisSecurityAltIdGroups.decode_encode]
  simp only [Option.bind_some]
  rw [IncrementalRefreshErisRelatedInstrumentsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode, Option.bind_some]
  rfl

end ErisReferenceDataGroup

/-- Eris Reference Data Groups -/
structure ErisReferenceDataGroups where
  blockLength : BitVec 16
  erisReferenceDataGroup : Bounded 1 ErisReferenceDataGroup
  deriving DecidableEq, Repr

namespace ErisReferenceDataGroups

def encode (message : ErisReferenceDataGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisReferenceDataGroup.val.length)
    ++ encodeMany ErisReferenceDataGroup.encode message.erisReferenceDataGroup.val

def decode (bytes : List UInt8) : Option (ErisReferenceDataGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisReferenceDataGroup_, bytes) ← decodeMany ErisReferenceDataGroup.decode numInGroup8.toNat bytes
  if fits_erisReferenceDataGroup : erisReferenceDataGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisReferenceDataGroup := ⟨erisReferenceDataGroup_, fits_erisReferenceDataGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisReferenceDataGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisReferenceDataGroups) : (encode message).length ≤ 7456968 := by
  have bound_erisReferenceDataGroup := message.erisReferenceDataGroup.length_lt
  have bound_erisReferenceDataGroup_items := encodeMany_length_le ErisReferenceDataGroup.encode 29243 ErisReferenceDataGroup.encode_length_le message.erisReferenceDataGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisReferenceDataGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisReferenceDataGroup.encode ErisReferenceDataGroup.decode ErisReferenceDataGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisReferenceDataGroup.length_lt, ↓reduceDIte]
  rfl

end ErisReferenceDataGroups

/-- Md Incremental Refresh Eris Reference Data And Daily Statistics -/
structure MdIncrementalRefreshErisReferenceDataAndDailyStatistics where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  erisReferenceDataGroups : ErisReferenceDataGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshErisReferenceDataAndDailyStatistics

def encode (message : MdIncrementalRefreshErisReferenceDataAndDailyStatistics) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ ErisReferenceDataGroups.encode message.erisReferenceDataGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshErisReferenceDataAndDailyStatistics × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (erisReferenceDataGroups, bytes) ← ErisReferenceDataGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, batchTotalMessagesOptional, erisReferenceDataGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshErisReferenceDataAndDailyStatistics) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshErisReferenceDataAndDailyStatistics) : (encode message).length ≤ 7456979 := by
  have bound_erisReferenceDataGroups := ErisReferenceDataGroups.encode_length_le message.erisReferenceDataGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshErisReferenceDataAndDailyStatistics) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ErisReferenceDataGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshErisReferenceDataAndDailyStatistics

/-- News Indices Related Sym Group: 50 bytes -/
structure NewsIndicesRelatedSymGroup where
  symbol : Alpha 50
  deriving DecidableEq, Repr

namespace NewsIndicesRelatedSymGroup

def encode (message : NewsIndicesRelatedSymGroup) : List UInt8 :=
  Alpha.encode message.symbol

def decode (bytes : List UInt8) : Option (NewsIndicesRelatedSymGroup × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 50 bytes
  pure ({ symbol }, bytes)

@[simp] theorem encode_length (message : NewsIndicesRelatedSymGroup) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewsIndicesRelatedSymGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsIndicesRelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewsIndicesRelatedSymGroup

/-- News Indices Related Sym Groups -/
structure NewsIndicesRelatedSymGroups where
  blockLength : BitVec 16
  newsIndicesRelatedSymGroup : Bounded 1 NewsIndicesRelatedSymGroup
  deriving DecidableEq, Repr

namespace NewsIndicesRelatedSymGroups

def encode (message : NewsIndicesRelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.newsIndicesRelatedSymGroup.val.length)
    ++ encodeMany NewsIndicesRelatedSymGroup.encode message.newsIndicesRelatedSymGroup.val

def decode (bytes : List UInt8) : Option (NewsIndicesRelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (newsIndicesRelatedSymGroup_, bytes) ← decodeMany NewsIndicesRelatedSymGroup.decode numInGroup8.toNat bytes
  if fits_newsIndicesRelatedSymGroup : newsIndicesRelatedSymGroup_.length < 256 ^ 1 then
    pure ({ blockLength, newsIndicesRelatedSymGroup := ⟨newsIndicesRelatedSymGroup_, fits_newsIndicesRelatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewsIndicesRelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewsIndicesRelatedSymGroups) : (encode message).length ≤ 12753 := by
  have bound_newsIndicesRelatedSymGroup := message.newsIndicesRelatedSymGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NewsIndicesRelatedSymGroup.encode 50 NewsIndicesRelatedSymGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : NewsIndicesRelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 NewsIndicesRelatedSymGroup.encode NewsIndicesRelatedSymGroup.decode NewsIndicesRelatedSymGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.newsIndicesRelatedSymGroup.length_lt, ↓reduceDIte]
  rfl

end NewsIndicesRelatedSymGroups

/-- Lines Of Text Group: 500 bytes -/
structure LinesOfTextGroup where
  text500 : Alpha 500
  deriving DecidableEq, Repr

namespace LinesOfTextGroup

def encode (message : LinesOfTextGroup) : List UInt8 :=
  Alpha.encode message.text500

def decode (bytes : List UInt8) : Option (LinesOfTextGroup × List UInt8) := do
  let (text500, bytes) ← Alpha.decode 500 bytes
  pure ({ text500 }, bytes)

@[simp] theorem encode_length (message : LinesOfTextGroup) : (encode message).length = 500 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LinesOfTextGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LinesOfTextGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LinesOfTextGroup

/-- Lines Of Text Groups -/
structure LinesOfTextGroups where
  blockLength : BitVec 16
  linesOfTextGroup : Bounded 1 LinesOfTextGroup
  deriving DecidableEq, Repr

namespace LinesOfTextGroups

def encode (message : LinesOfTextGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.linesOfTextGroup.val.length)
    ++ encodeMany LinesOfTextGroup.encode message.linesOfTextGroup.val

def decode (bytes : List UInt8) : Option (LinesOfTextGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (linesOfTextGroup_, bytes) ← decodeMany LinesOfTextGroup.decode numInGroup8.toNat bytes
  if fits_linesOfTextGroup : linesOfTextGroup_.length < 256 ^ 1 then
    pure ({ blockLength, linesOfTextGroup := ⟨linesOfTextGroup_, fits_linesOfTextGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : LinesOfTextGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LinesOfTextGroups) : (encode message).length ≤ 127503 := by
  have bound_linesOfTextGroup := message.linesOfTextGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LinesOfTextGroup.encode 500 LinesOfTextGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : LinesOfTextGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 LinesOfTextGroup.encode LinesOfTextGroup.decode LinesOfTextGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.linesOfTextGroup.length_lt, ↓reduceDIte]
  rfl

end LinesOfTextGroups

/-- Md News Indices -/
structure MdNewsIndices where
  headline : Alpha 50
  origTime : BitVec 64
  mdFeedType : Alpha 2
  newsIndicesRelatedSymGroups : NewsIndicesRelatedSymGroups
  linesOfTextGroups : LinesOfTextGroups
  deriving DecidableEq, Repr

namespace MdNewsIndices

def encode (message : MdNewsIndices) : List UInt8 :=
  Alpha.encode message.headline
    ++ encodeUIntLE 8 message.origTime
    ++ Alpha.encode message.mdFeedType
    ++ NewsIndicesRelatedSymGroups.encode message.newsIndicesRelatedSymGroups
    ++ LinesOfTextGroups.encode message.linesOfTextGroups

def decode (bytes : List UInt8) : Option (MdNewsIndices × List UInt8) := do
  let (headline, bytes) ← Alpha.decode 50 bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (mdFeedType, bytes) ← Alpha.decode 2 bytes
  let (newsIndicesRelatedSymGroups, bytes) ← NewsIndicesRelatedSymGroups.decode bytes
  let (linesOfTextGroups, bytes) ← LinesOfTextGroups.decode bytes
  pure ({ headline, origTime, mdFeedType, newsIndicesRelatedSymGroups, linesOfTextGroups }, bytes)

theorem encode_length_pos (message : MdNewsIndices) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdNewsIndices) : (encode message).length ≤ 140316 := by
  have bound_newsIndicesRelatedSymGroups := NewsIndicesRelatedSymGroups.encode_length_le message.newsIndicesRelatedSymGroups
  have bound_linesOfTextGroups := LinesOfTextGroups.encode_length_le message.linesOfTextGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdNewsIndices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NewsIndicesRelatedSymGroups.decode_encode]
  simp only [Option.bind_some]
  rw [LinesOfTextGroups.decode_encode, Option.bind_some]
  rfl

end MdNewsIndices

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MaturityMonthYear

/-- Underlying Maturity Month Year: 5 bytes -/
structure UnderlyingMaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace UnderlyingMaturityMonthYear

def encode (message : UnderlyingMaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (UnderlyingMaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : UnderlyingMaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UnderlyingMaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingMaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end UnderlyingMaturityMonthYear

/-- Trade Blocks Underlyings Group: 68 bytes -/
structure TradeBlocksUnderlyingsGroup where
  underlyingSymbol : Alpha 50
  underlyingMaturityMonthYear : UnderlyingMaturityMonthYear
  underlyingSecurityType : Alpha 9
  underlyingSecurityExchangeString4 : Alpha 4
  deriving DecidableEq, Repr

namespace TradeBlocksUnderlyingsGroup

def encode (message : TradeBlocksUnderlyingsGroup) : List UInt8 :=
  Alpha.encode message.underlyingSymbol
    ++ UnderlyingMaturityMonthYear.encode message.underlyingMaturityMonthYear
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingSecurityExchangeString4

def decode (bytes : List UInt8) : Option (TradeBlocksUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbol, bytes) ← Alpha.decode 50 bytes
  let (underlyingMaturityMonthYear, bytes) ← UnderlyingMaturityMonthYear.decode bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 9 bytes
  let (underlyingSecurityExchangeString4, bytes) ← Alpha.decode 4 bytes
  pure ({ underlyingSymbol, underlyingMaturityMonthYear, underlyingSecurityType, underlyingSecurityExchangeString4 }, bytes)

@[simp] theorem encode_length (message : TradeBlocksUnderlyingsGroup) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, UnderlyingMaturityMonthYear.encode_length]

theorem encode_length_pos (message : TradeBlocksUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBlocksUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [UnderlyingMaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeBlocksUnderlyingsGroup

/-- Trade Blocks Underlyings Groups -/
structure TradeBlocksUnderlyingsGroups where
  blockLength : BitVec 16
  tradeBlocksUnderlyingsGroup : Bounded 1 TradeBlocksUnderlyingsGroup
  deriving DecidableEq, Repr

namespace TradeBlocksUnderlyingsGroups

def encode (message : TradeBlocksUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksUnderlyingsGroup.val.length)
    ++ encodeMany TradeBlocksUnderlyingsGroup.encode message.tradeBlocksUnderlyingsGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksUnderlyingsGroup_, bytes) ← decodeMany TradeBlocksUnderlyingsGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksUnderlyingsGroup : tradeBlocksUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksUnderlyingsGroup := ⟨tradeBlocksUnderlyingsGroup_, fits_tradeBlocksUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksUnderlyingsGroups) : (encode message).length ≤ 17343 := by
  have bound_tradeBlocksUnderlyingsGroup := message.tradeBlocksUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeBlocksUnderlyingsGroup.encode 68 TradeBlocksUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksUnderlyingsGroup.encode TradeBlocksUnderlyingsGroup.decode TradeBlocksUnderlyingsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksUnderlyingsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksUnderlyingsGroups

/-- Trade Blocks Party Ids Group: 52 bytes -/
structure TradeBlocksPartyIdsGroup where
  partyId : Alpha 50
  partyRole : Alpha 2
  deriving DecidableEq, Repr

namespace TradeBlocksPartyIdsGroup

def encode (message : TradeBlocksPartyIdsGroup) : List UInt8 :=
  Alpha.encode message.partyId
    ++ Alpha.encode message.partyRole

def decode (bytes : List UInt8) : Option (TradeBlocksPartyIdsGroup × List UInt8) := do
  let (partyId, bytes) ← Alpha.decode 50 bytes
  let (partyRole, bytes) ← Alpha.decode 2 bytes
  pure ({ partyId, partyRole }, bytes)

@[simp] theorem encode_length (message : TradeBlocksPartyIdsGroup) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradeBlocksPartyIdsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBlocksPartyIdsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeBlocksPartyIdsGroup

/-- Trade Blocks Party Ids Groups -/
structure TradeBlocksPartyIdsGroups where
  blockLength : BitVec 16
  tradeBlocksPartyIdsGroup : Bounded 1 TradeBlocksPartyIdsGroup
  deriving DecidableEq, Repr

namespace TradeBlocksPartyIdsGroups

def encode (message : TradeBlocksPartyIdsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksPartyIdsGroup.val.length)
    ++ encodeMany TradeBlocksPartyIdsGroup.encode message.tradeBlocksPartyIdsGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksPartyIdsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksPartyIdsGroup_, bytes) ← decodeMany TradeBlocksPartyIdsGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksPartyIdsGroup : tradeBlocksPartyIdsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksPartyIdsGroup := ⟨tradeBlocksPartyIdsGroup_, fits_tradeBlocksPartyIdsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksPartyIdsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksPartyIdsGroups) : (encode message).length ≤ 13263 := by
  have bound_tradeBlocksPartyIdsGroup := message.tradeBlocksPartyIdsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeBlocksPartyIdsGroup.encode 52 TradeBlocksPartyIdsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksPartyIdsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksPartyIdsGroup.encode TradeBlocksPartyIdsGroup.decode TradeBlocksPartyIdsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksPartyIdsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksPartyIdsGroups

/-- Leg Maturity Month Year: 5 bytes -/
structure LegMaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace LegMaturityMonthYear

def encode (message : LegMaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (LegMaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : LegMaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegMaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegMaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegMaturityMonthYear

/-- Trade Blocks Original Legs Group: 135 bytes -/
structure TradeBlocksOriginalLegsGroup where
  legSymbol : Alpha 50
  legSecurityId : BitVec 64
  legSecurityGroup : Alpha 12
  legId : Alpha 17
  legSecurityType : Alpha 9
  legMaturityMonthYear : LegMaturityMonthYear
  legMaturityDate : BitVec 16
  legStrikePricePricenull : BitVec 64
  legUnitOfMeasure : Alpha 5
  legUnitOfMeasureQtyPricenull : BitVec 64
  legSecurityExchange : Alpha 4
  legRatioQtyUInt16Null : BitVec 16
  legSide : BitVec 8
  legPutOrCall : BitVec 8
  legUnitOfMeasureCurrency : Alpha 3
  deriving DecidableEq, Repr

namespace TradeBlocksOriginalLegsGroup

def encode (message : TradeBlocksOriginalLegsGroup) : List UInt8 :=
  Alpha.encode message.legSymbol
    ++ encodeUIntLE 8 message.legSecurityId
    ++ Alpha.encode message.legSecurityGroup
    ++ Alpha.encode message.legId
    ++ Alpha.encode message.legSecurityType
    ++ LegMaturityMonthYear.encode message.legMaturityMonthYear
    ++ encodeUIntLE 2 message.legMaturityDate
    ++ encodeUIntLE 8 message.legStrikePricePricenull
    ++ Alpha.encode message.legUnitOfMeasure
    ++ encodeUIntLE 8 message.legUnitOfMeasureQtyPricenull
    ++ Alpha.encode message.legSecurityExchange
    ++ encodeUIntLE 2 message.legRatioQtyUInt16Null
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legPutOrCall
    ++ Alpha.encode message.legUnitOfMeasureCurrency

def decode (bytes : List UInt8) : Option (TradeBlocksOriginalLegsGroup × List UInt8) := do
  let (legSymbol, bytes) ← Alpha.decode 50 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityGroup, bytes) ← Alpha.decode 12 bytes
  let (legId, bytes) ← Alpha.decode 17 bytes
  let (legSecurityType, bytes) ← Alpha.decode 9 bytes
  let (legMaturityMonthYear, bytes) ← LegMaturityMonthYear.decode bytes
  let (legMaturityDate, bytes) ← decodeUIntLE 2 bytes
  let (legStrikePricePricenull, bytes) ← decodeUIntLE 8 bytes
  let (legUnitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (legUnitOfMeasureQtyPricenull, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityExchange, bytes) ← Alpha.decode 4 bytes
  let (legRatioQtyUInt16Null, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legPutOrCall, bytes) ← decodeUInt 1 bytes
  let (legUnitOfMeasureCurrency, bytes) ← Alpha.decode 3 bytes
  pure ({ legSymbol, legSecurityId, legSecurityGroup, legId, legSecurityType, legMaturityMonthYear, legMaturityDate, legStrikePricePricenull, legUnitOfMeasure, legUnitOfMeasureQtyPricenull, legSecurityExchange, legRatioQtyUInt16Null, legSide, legPutOrCall, legUnitOfMeasureCurrency }, bytes)

@[simp] theorem encode_length (message : TradeBlocksOriginalLegsGroup) : (encode message).length = 135 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, LegMaturityMonthYear.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBlocksOriginalLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBlocksOriginalLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [LegMaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeBlocksOriginalLegsGroup

/-- Trade Blocks Original Legs Groups -/
structure TradeBlocksOriginalLegsGroups where
  blockLength : BitVec 16
  tradeBlocksOriginalLegsGroup : Bounded 1 TradeBlocksOriginalLegsGroup
  deriving DecidableEq, Repr

namespace TradeBlocksOriginalLegsGroups

def encode (message : TradeBlocksOriginalLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksOriginalLegsGroup.val.length)
    ++ encodeMany TradeBlocksOriginalLegsGroup.encode message.tradeBlocksOriginalLegsGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksOriginalLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksOriginalLegsGroup_, bytes) ← decodeMany TradeBlocksOriginalLegsGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksOriginalLegsGroup : tradeBlocksOriginalLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksOriginalLegsGroup := ⟨tradeBlocksOriginalLegsGroup_, fits_tradeBlocksOriginalLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksOriginalLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksOriginalLegsGroups) : (encode message).length ≤ 34428 := by
  have bound_tradeBlocksOriginalLegsGroup := message.tradeBlocksOriginalLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeBlocksOriginalLegsGroup.encode 135 TradeBlocksOriginalLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksOriginalLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksOriginalLegsGroup.encode TradeBlocksOriginalLegsGroup.decode TradeBlocksOriginalLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksOriginalLegsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksOriginalLegsGroups

/-- Trade Blocks Original Group -/
structure TradeBlocksOriginalGroup where
  mdUpdateAction : BitVec 8
  securityId : BitVec 64
  rptSeq : BitVec 32
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 64
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  symbol : Alpha 50
  securityGroup12 : Alpha 12
  securityType : Alpha 9
  securitySubType : Alpha 2
  maturityMonthYear : MaturityMonthYear
  securityExchange4 : Alpha 4
  maturityDate : BitVec 16
  unitOfMeasure : Alpha 5
  unitOfMeasureCurrency3 : Alpha 3
  unitOfMeasureQtyOptional : BitVec 64
  couponRate : BitVec 32
  priceType : BitVec 16
  trdType : BitVec 8
  mdEntryId : Alpha 26
  putOrCall : BitVec 8
  strikePrice : BitVec 64
  restructuringType : Alpha 2
  seniority : Alpha 2
  referenceId100 : Alpha 100
  strategyLinkId : Alpha 26
  legRefId : Alpha 17
  tradeBlocksUnderlyingsGroups : TradeBlocksUnderlyingsGroups
  tradeBlocksPartyIdsGroups : TradeBlocksPartyIdsGroups
  tradeBlocksOriginalLegsGroups : TradeBlocksOriginalLegsGroups
  deriving DecidableEq, Repr

namespace TradeBlocksOriginalGroup

def encode (message : TradeBlocksOriginalGroup) : List UInt8 :=
  encodeUInt 1 message.mdUpdateAction
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.mdEntryPxOptional
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup12
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securitySubType
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.securityExchange4
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.unitOfMeasure
    ++ Alpha.encode message.unitOfMeasureCurrency3
    ++ encodeUIntLE 8 message.unitOfMeasureQtyOptional
    ++ encodeUIntLE 4 message.couponRate
    ++ encodeUIntLE 2 message.priceType
    ++ encodeUInt 1 message.trdType
    ++ Alpha.encode message.mdEntryId
    ++ encodeUInt 1 message.putOrCall
    ++ encodeUIntLE 8 message.strikePrice
    ++ Alpha.encode message.restructuringType
    ++ Alpha.encode message.seniority
    ++ Alpha.encode message.referenceId100
    ++ Alpha.encode message.strategyLinkId
    ++ Alpha.encode message.legRefId
    ++ TradeBlocksUnderlyingsGroups.encode message.tradeBlocksUnderlyingsGroups
    ++ TradeBlocksPartyIdsGroups.encode message.tradeBlocksPartyIdsGroups
    ++ TradeBlocksOriginalLegsGroups.encode message.tradeBlocksOriginalLegsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBlocksOriginalGroup × List UInt8) := do
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (securityExchange4, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureCurrency3, bytes) ← Alpha.decode 3 bytes
  let (unitOfMeasureQtyOptional, bytes) ← decodeUIntLE 8 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (priceType, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUInt 1 bytes
  let (mdEntryId, bytes) ← Alpha.decode 26 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (restructuringType, bytes) ← Alpha.decode 2 bytes
  let (seniority, bytes) ← Alpha.decode 2 bytes
  let (referenceId100, bytes) ← Alpha.decode 100 bytes
  let (strategyLinkId, bytes) ← Alpha.decode 26 bytes
  let (legRefId, bytes) ← Alpha.decode 17 bytes
  let (tradeBlocksUnderlyingsGroups, bytes) ← TradeBlocksUnderlyingsGroups.decode bytes
  let (tradeBlocksPartyIdsGroups, bytes) ← TradeBlocksPartyIdsGroups.decode bytes
  let (tradeBlocksOriginalLegsGroups, bytes) ← TradeBlocksOriginalLegsGroups.decode bytes
  pure ({ mdUpdateAction, securityId, rptSeq, mdEntryPxOptional, mdEntrySizeOptional, numberOfOrders, tradeId, aggressorSide, symbol, securityGroup12, securityType, securitySubType, maturityMonthYear, securityExchange4, maturityDate, unitOfMeasure, unitOfMeasureCurrency3, unitOfMeasureQtyOptional, couponRate, priceType, trdType, mdEntryId, putOrCall, strikePrice, restructuringType, seniority, referenceId100, strategyLinkId, legRefId, tradeBlocksUnderlyingsGroups, tradeBlocksPartyIdsGroups, tradeBlocksOriginalLegsGroups }, bytes)

theorem encode_length_pos (message : TradeBlocksOriginalGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksOriginalGroup) : (encode message).length ≤ 65361 := by
  have bound_tradeBlocksUnderlyingsGroups := TradeBlocksUnderlyingsGroups.encode_length_le message.tradeBlocksUnderlyingsGroups
  have bound_tradeBlocksPartyIdsGroups := TradeBlocksPartyIdsGroups.encode_length_le message.tradeBlocksPartyIdsGroups
  have bound_tradeBlocksOriginalLegsGroups := TradeBlocksOriginalLegsGroups.encode_length_le message.tradeBlocksOriginalLegsGroups
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksOriginalGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksPartyIdsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksOriginalLegsGroups.decode_encode, Option.bind_some]
  rfl

end TradeBlocksOriginalGroup

/-- Trade Blocks Original Groups -/
structure TradeBlocksOriginalGroups where
  blockLength : BitVec 16
  tradeBlocksOriginalGroup : Bounded 1 TradeBlocksOriginalGroup
  deriving DecidableEq, Repr

namespace TradeBlocksOriginalGroups

def encode (message : TradeBlocksOriginalGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksOriginalGroup.val.length)
    ++ encodeMany TradeBlocksOriginalGroup.encode message.tradeBlocksOriginalGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksOriginalGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksOriginalGroup_, bytes) ← decodeMany TradeBlocksOriginalGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksOriginalGroup : tradeBlocksOriginalGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksOriginalGroup := ⟨tradeBlocksOriginalGroup_, fits_tradeBlocksOriginalGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksOriginalGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksOriginalGroups) : (encode message).length ≤ 16667058 := by
  have bound_tradeBlocksOriginalGroup := message.tradeBlocksOriginalGroup.length_lt
  have bound_tradeBlocksOriginalGroup_items := encodeMany_length_le TradeBlocksOriginalGroup.encode 65361 TradeBlocksOriginalGroup.encode_length_le message.tradeBlocksOriginalGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksOriginalGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksOriginalGroup.encode TradeBlocksOriginalGroup.decode TradeBlocksOriginalGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksOriginalGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksOriginalGroups

/-- Md Incremental Refresh Trade Blocks 340 -/
structure MdIncrementalRefreshTradeBlocks340 where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessages : BitVec 16
  tradeBlocksOriginalGroups : TradeBlocksOriginalGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeBlocks340

def encode (message : MdIncrementalRefreshTradeBlocks340) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessages
    ++ TradeBlocksOriginalGroups.encode message.tradeBlocksOriginalGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeBlocks340 × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessages, bytes) ← decodeUIntLE 2 bytes
  let (tradeBlocksOriginalGroups, bytes) ← TradeBlocksOriginalGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, batchTotalMessages, tradeBlocksOriginalGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeBlocks340) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeBlocks340) : (encode message).length ≤ 16667069 := by
  have bound_tradeBlocksOriginalGroups := TradeBlocksOriginalGroups.encode_length_le message.tradeBlocksOriginalGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeBlocks340) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [TradeBlocksOriginalGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshTradeBlocks340

/-- Quote Request Related Sym Group -/
structure QuoteRequestRelatedSymGroup where
  symbol : Alpha 50
  couponRate : BitVec 32
  orderQty : BitVec 64
  securityExchange : Alpha 4
  productOptional : BitVec 8
  securityGroup26 : Alpha 26
  maturityDate : BitVec 16
  securityType4 : Alpha 4
  quoteType : BitVec 8
  eventsGroups : EventsGroups
  deriving DecidableEq, Repr

namespace QuoteRequestRelatedSymGroup

def encode (message : QuoteRequestRelatedSymGroup) : List UInt8 :=
  Alpha.encode message.symbol
    ++ encodeUIntLE 4 message.couponRate
    ++ encodeUIntLE 8 message.orderQty
    ++ Alpha.encode message.securityExchange
    ++ encodeUInt 1 message.productOptional
    ++ Alpha.encode message.securityGroup26
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.securityType4
    ++ encodeUInt 1 message.quoteType
    ++ EventsGroups.encode message.eventsGroups

def decode (bytes : List UInt8) : Option (QuoteRequestRelatedSymGroup × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (securityGroup26, bytes) ← Alpha.decode 26 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (securityType4, bytes) ← Alpha.decode 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  pure ({ symbol, couponRate, orderQty, securityExchange, productOptional, securityGroup26, maturityDate, securityType4, quoteType, eventsGroups }, bytes)

theorem encode_length_pos (message : QuoteRequestRelatedSymGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequestRelatedSymGroup) : (encode message).length ≤ 2398 := by
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequestRelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode, Option.bind_some]
  rfl

end QuoteRequestRelatedSymGroup

/-- Quote Request Related Sym Groups -/
structure QuoteRequestRelatedSymGroups where
  blockLength : BitVec 16
  quoteRequestRelatedSymGroup : Bounded 1 QuoteRequestRelatedSymGroup
  deriving DecidableEq, Repr

namespace QuoteRequestRelatedSymGroups

def encode (message : QuoteRequestRelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteRequestRelatedSymGroup.val.length)
    ++ encodeMany QuoteRequestRelatedSymGroup.encode message.quoteRequestRelatedSymGroup.val

def decode (bytes : List UInt8) : Option (QuoteRequestRelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (quoteRequestRelatedSymGroup_, bytes) ← decodeMany QuoteRequestRelatedSymGroup.decode numInGroup8.toNat bytes
  if fits_quoteRequestRelatedSymGroup : quoteRequestRelatedSymGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteRequestRelatedSymGroup := ⟨quoteRequestRelatedSymGroup_, fits_quoteRequestRelatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteRequestRelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequestRelatedSymGroups) : (encode message).length ≤ 611493 := by
  have bound_quoteRequestRelatedSymGroup := message.quoteRequestRelatedSymGroup.length_lt
  have bound_quoteRequestRelatedSymGroup_items := encodeMany_length_le QuoteRequestRelatedSymGroup.encode 2398 QuoteRequestRelatedSymGroup.encode_length_le message.quoteRequestRelatedSymGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequestRelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteRequestRelatedSymGroup.encode QuoteRequestRelatedSymGroup.decode QuoteRequestRelatedSymGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteRequestRelatedSymGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteRequestRelatedSymGroups

/-- Quote Request -/
structure QuoteRequest where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  quoteReqId : Alpha 26
  quoteRequestRelatedSymGroups : QuoteRequestRelatedSymGroups
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.quoteReqId
    ++ QuoteRequestRelatedSymGroups.encode message.quoteRequestRelatedSymGroups

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (quoteReqId, bytes) ← Alpha.decode 26 bytes
  let (quoteRequestRelatedSymGroups, bytes) ← QuoteRequestRelatedSymGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, quoteReqId, quoteRequestRelatedSymGroups }, bytes)

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteRequest) : (encode message).length ≤ 611528 := by
  have bound_quoteRequestRelatedSymGroups := QuoteRequestRelatedSymGroups.encode_length_le message.quoteRequestRelatedSymGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [QuoteRequestRelatedSymGroups.decode_encode, Option.bind_some]
  rfl

end QuoteRequest

/-- Inst Attrib Group: 101 bytes -/
structure InstAttribGroup where
  instAttribType : BitVec 8
  instAttribValue : Alpha 100
  deriving DecidableEq, Repr

namespace InstAttribGroup

def encode (message : InstAttribGroup) : List UInt8 :=
  encodeUInt 1 message.instAttribType
    ++ Alpha.encode message.instAttribValue

def decode (bytes : List UInt8) : Option (InstAttribGroup × List UInt8) := do
  let (instAttribType, bytes) ← decodeUInt 1 bytes
  let (instAttribValue, bytes) ← Alpha.decode 100 bytes
  pure ({ instAttribType, instAttribValue }, bytes)

@[simp] theorem encode_length (message : InstAttribGroup) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstAttribGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstAttribGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InstAttribGroup

/-- Inst Attrib Groups -/
structure InstAttribGroups where
  blockLength : BitVec 16
  instAttribGroup : Bounded 2 InstAttribGroup
  deriving DecidableEq, Repr

namespace InstAttribGroups

def encode (message : InstAttribGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instAttribGroup.val.length)
    ++ encodeMany InstAttribGroup.encode message.instAttribGroup.val

def decode (bytes : List UInt8) : Option (InstAttribGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (instAttribGroup_, bytes) ← decodeMany InstAttribGroup.decode numInGroup.toNat bytes
  if fits_instAttribGroup : instAttribGroup_.length < 256 ^ 2 then
    pure ({ blockLength, instAttribGroup := ⟨instAttribGroup_, fits_instAttribGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstAttribGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstAttribGroups) : (encode message).length ≤ 6619039 := by
  have bound_instAttribGroup := message.instAttribGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const InstAttribGroup.encode 101 InstAttribGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : InstAttribGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 InstAttribGroup.encode InstAttribGroup.decode InstAttribGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.instAttribGroup.length_lt, ↓reduceDIte]
  rfl

end InstAttribGroups

/-- Md Instrument Definition Indices -/
structure MdInstrumentDefinitionIndices where
  symbol : Alpha 50
  product : BitVec 8
  securityExchange : Alpha 4
  currency : Alpha 3
  securityUpdateAction : SecurityUpdateAction
  mdFeedType : Alpha 2
  applId : BitVec 16
  instAttribGroups : InstAttribGroups
  eventsGroups : EventsGroups
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionIndices

def encode (message : MdInstrumentDefinitionIndices) : List UInt8 :=
  Alpha.encode message.symbol
    ++ encodeUInt 1 message.product
    ++ Alpha.encode message.securityExchange
    ++ Alpha.encode message.currency
    ++ SecurityUpdateAction.encode message.securityUpdateAction
    ++ Alpha.encode message.mdFeedType
    ++ encodeUIntLE 2 message.applId
    ++ InstAttribGroups.encode message.instAttribGroups
    ++ EventsGroups.encode message.eventsGroups

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionIndices × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (product, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (mdFeedType, bytes) ← Alpha.decode 2 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (instAttribGroups, bytes) ← InstAttribGroups.decode bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  pure ({ symbol, product, securityExchange, currency, securityUpdateAction, mdFeedType, applId, instAttribGroups, eventsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionIndices) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionIndices) : (encode message).length ≤ 6621400 := by
  have bound_instAttribGroups := InstAttribGroups.encode_length_le message.instAttribGroups
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SecurityUpdateAction.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionIndices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [InstAttribGroups.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode, Option.bind_some]
  rfl

end MdInstrumentDefinitionIndices

/-- Md Entry Px Decimal: 9 bytes -/
structure MdEntryPxDecimal where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MdEntryPxDecimal

def encode (message : MdEntryPxDecimal) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MdEntryPxDecimal × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MdEntryPxDecimal) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MdEntryPxDecimal) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdEntryPxDecimal) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MdEntryPxDecimal

/-- Yield: 9 bytes -/
structure Yield where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace Yield

def encode (message : Yield) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (Yield × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : Yield) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Yield) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Yield) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Yield

/-- Net Chg Prev Day: 9 bytes -/
structure NetChgPrevDay where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace NetChgPrevDay

def encode (message : NetChgPrevDay) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (NetChgPrevDay × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : NetChgPrevDay) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NetChgPrevDay) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChgPrevDay) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NetChgPrevDay

/-- Net Pct Chg: 9 bytes -/
structure NetPctChg where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace NetPctChg

def encode (message : NetPctChg) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (NetPctChg × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : NetPctChg) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NetPctChg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetPctChg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NetPctChg

/-- Percent Trading: 9 bytes -/
structure PercentTrading where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace PercentTrading

def encode (message : PercentTrading) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (PercentTrading × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : PercentTrading) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PercentTrading) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PercentTrading) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end PercentTrading

/-- Incremental Refresh Indices Group: 176 bytes -/
structure IncrementalRefreshIndicesGroup where
  mdEntryTypeIndices : MdEntryTypeIndices
  rptSeq : BitVec 32
  mdEntryPxDecimal : MdEntryPxDecimal
  mdEntrySizeOptional : BitVec 64
  symbol : Alpha 50
  openCloseSettlFlag : BitVec 8
  yieldType : Alpha 8
  yield : Yield
  netChgPrevDay : NetChgPrevDay
  netPctChg : NetPctChg
  percentTrading : PercentTrading
  mdEntryCode : BitVec 8
  mdEntryDate : BitVec 32
  mdEntryTime : BitVec 32
  referenceId50 : Alpha 50
  deriving DecidableEq, Repr

namespace IncrementalRefreshIndicesGroup

def encode (message : IncrementalRefreshIndicesGroup) : List UInt8 :=
  MdEntryTypeIndices.encode message.mdEntryTypeIndices
    ++ encodeUIntLE 4 message.rptSeq
    ++ MdEntryPxDecimal.encode message.mdEntryPxDecimal
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ Alpha.encode message.symbol
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ Alpha.encode message.yieldType
    ++ Yield.encode message.yield
    ++ NetChgPrevDay.encode message.netChgPrevDay
    ++ NetPctChg.encode message.netPctChg
    ++ PercentTrading.encode message.percentTrading
    ++ encodeUInt 1 message.mdEntryCode
    ++ encodeUIntLE 4 message.mdEntryDate
    ++ encodeUIntLE 4 message.mdEntryTime
    ++ Alpha.encode message.referenceId50

def decode (bytes : List UInt8) : Option (IncrementalRefreshIndicesGroup × List UInt8) := do
  let (mdEntryTypeIndices, bytes) ← MdEntryTypeIndices.decode bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxDecimal, bytes) ← MdEntryPxDecimal.decode bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (yieldType, bytes) ← Alpha.decode 8 bytes
  let (yield, bytes) ← Yield.decode bytes
  let (netChgPrevDay, bytes) ← NetChgPrevDay.decode bytes
  let (netPctChg, bytes) ← NetPctChg.decode bytes
  let (percentTrading, bytes) ← PercentTrading.decode bytes
  let (mdEntryCode, bytes) ← decodeUInt 1 bytes
  let (mdEntryDate, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryTime, bytes) ← decodeUIntLE 4 bytes
  let (referenceId50, bytes) ← Alpha.decode 50 bytes
  pure ({ mdEntryTypeIndices, rptSeq, mdEntryPxDecimal, mdEntrySizeOptional, symbol, openCloseSettlFlag, yieldType, yield, netChgPrevDay, netPctChg, percentTrading, mdEntryCode, mdEntryDate, mdEntryTime, referenceId50 }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshIndicesGroup) : (encode message).length = 176 := by
  unfold encode
  simp only [List.length_append, MdEntryTypeIndices.encode_length, encodeUIntLE_length, MdEntryPxDecimal.encode_length, Alpha.encode_length, encodeUInt_length, Yield.encode_length, NetChgPrevDay.encode_length, NetPctChg.encode_length, PercentTrading.encode_length]

theorem encode_length_pos (message : IncrementalRefreshIndicesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshIndicesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [MdEntryTypeIndices.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryPxDecimal.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Yield.decode_encode]
  simp only [Option.bind_some]
  rw [NetChgPrevDay.decode_encode]
  simp only [Option.bind_some]
  rw [NetPctChg.decode_encode]
  simp only [Option.bind_some]
  rw [PercentTrading.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshIndicesGroup

/-- Incremental Refresh Indices Groups -/
structure IncrementalRefreshIndicesGroups where
  blockLength : BitVec 16
  incrementalRefreshIndicesGroup : Bounded 1 IncrementalRefreshIndicesGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshIndicesGroups

def encode (message : IncrementalRefreshIndicesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshIndicesGroup.val.length)
    ++ encodeMany IncrementalRefreshIndicesGroup.encode message.incrementalRefreshIndicesGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshIndicesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshIndicesGroup_, bytes) ← decodeMany IncrementalRefreshIndicesGroup.decode numInGroup8.toNat bytes
  if fits_incrementalRefreshIndicesGroup : incrementalRefreshIndicesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshIndicesGroup := ⟨incrementalRefreshIndicesGroup_, fits_incrementalRefreshIndicesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshIndicesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshIndicesGroups) : (encode message).length ≤ 44883 := by
  have bound_incrementalRefreshIndicesGroup := message.incrementalRefreshIndicesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshIndicesGroup.encode 176 IncrementalRefreshIndicesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshIndicesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 IncrementalRefreshIndicesGroup.encode IncrementalRefreshIndicesGroup.decode IncrementalRefreshIndicesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.incrementalRefreshIndicesGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshIndicesGroups

/-- Md Incremental Refresh Indices -/
structure MdIncrementalRefreshIndices where
  transactTime : BitVec 64
  mdFeedType : Alpha 2
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  incrementalRefreshIndicesGroups : IncrementalRefreshIndicesGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshIndices

def encode (message : MdIncrementalRefreshIndices) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ Alpha.encode message.mdFeedType
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ IncrementalRefreshIndicesGroups.encode message.incrementalRefreshIndicesGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshIndices × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mdFeedType, bytes) ← Alpha.decode 2 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (incrementalRefreshIndicesGroups, bytes) ← IncrementalRefreshIndicesGroups.decode bytes
  pure ({ transactTime, mdFeedType, matchEventIndicator, batchTotalMessagesOptional, incrementalRefreshIndicesGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshIndices) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshIndices) : (encode message).length ≤ 44896 := by
  have bound_incrementalRefreshIndicesGroups := IncrementalRefreshIndicesGroups.encode_length_le message.incrementalRefreshIndicesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshIndices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [IncrementalRefreshIndicesGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshIndices

/-- Md Entry Size: 9 bytes -/
structure MdEntrySize where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MdEntrySize

def encode (message : MdEntrySize) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MdEntrySize × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MdEntrySize) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MdEntrySize) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdEntrySize) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MdEntrySize

/-- Trade Blocks Legacy Group -/
structure TradeBlocksLegacyGroup where
  mdUpdateAction : BitVec 8
  securityId : BitVec 64
  rptSeq : BitVec 32
  mdEntryPxOptional : BitVec 64
  mdEntrySize : MdEntrySize
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  symbol : Alpha 50
  securityGroup12 : Alpha 12
  securityType : Alpha 9
  securitySubType : Alpha 2
  maturityMonthYear : MaturityMonthYear
  securityExchange4 : Alpha 4
  maturityDate : BitVec 16
  unitOfMeasure : Alpha 5
  unitOfMeasureCurrency3 : Alpha 3
  unitOfMeasureQtyOptional : BitVec 64
  couponRate : BitVec 32
  priceType : BitVec 16
  trdType : BitVec 8
  mdEntryId : Alpha 26
  putOrCall : BitVec 8
  strikePrice : BitVec 64
  restructuringType : Alpha 2
  seniority : Alpha 2
  referenceId100 : Alpha 100
  strategyLinkId : Alpha 26
  legRefId : Alpha 17
  tradeBlocksUnderlyingsGroups : TradeBlocksUnderlyingsGroups
  tradeBlocksPartyIdsGroups : TradeBlocksPartyIdsGroups
  tradeBlocksOriginalLegsGroups : TradeBlocksOriginalLegsGroups
  deriving DecidableEq, Repr

namespace TradeBlocksLegacyGroup

def encode (message : TradeBlocksLegacyGroup) : List UInt8 :=
  encodeUInt 1 message.mdUpdateAction
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.mdEntryPxOptional
    ++ MdEntrySize.encode message.mdEntrySize
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup12
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securitySubType
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.securityExchange4
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.unitOfMeasure
    ++ Alpha.encode message.unitOfMeasureCurrency3
    ++ encodeUIntLE 8 message.unitOfMeasureQtyOptional
    ++ encodeUIntLE 4 message.couponRate
    ++ encodeUIntLE 2 message.priceType
    ++ encodeUInt 1 message.trdType
    ++ Alpha.encode message.mdEntryId
    ++ encodeUInt 1 message.putOrCall
    ++ encodeUIntLE 8 message.strikePrice
    ++ Alpha.encode message.restructuringType
    ++ Alpha.encode message.seniority
    ++ Alpha.encode message.referenceId100
    ++ Alpha.encode message.strategyLinkId
    ++ Alpha.encode message.legRefId
    ++ TradeBlocksUnderlyingsGroups.encode message.tradeBlocksUnderlyingsGroups
    ++ TradeBlocksPartyIdsGroups.encode message.tradeBlocksPartyIdsGroups
    ++ TradeBlocksOriginalLegsGroups.encode message.tradeBlocksOriginalLegsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBlocksLegacyGroup × List UInt8) := do
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← MdEntrySize.decode bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (securityExchange4, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureCurrency3, bytes) ← Alpha.decode 3 bytes
  let (unitOfMeasureQtyOptional, bytes) ← decodeUIntLE 8 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (priceType, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUInt 1 bytes
  let (mdEntryId, bytes) ← Alpha.decode 26 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (restructuringType, bytes) ← Alpha.decode 2 bytes
  let (seniority, bytes) ← Alpha.decode 2 bytes
  let (referenceId100, bytes) ← Alpha.decode 100 bytes
  let (strategyLinkId, bytes) ← Alpha.decode 26 bytes
  let (legRefId, bytes) ← Alpha.decode 17 bytes
  let (tradeBlocksUnderlyingsGroups, bytes) ← TradeBlocksUnderlyingsGroups.decode bytes
  let (tradeBlocksPartyIdsGroups, bytes) ← TradeBlocksPartyIdsGroups.decode bytes
  let (tradeBlocksOriginalLegsGroups, bytes) ← TradeBlocksOriginalLegsGroups.decode bytes
  pure ({ mdUpdateAction, securityId, rptSeq, mdEntryPxOptional, mdEntrySize, numberOfOrders, tradeId, aggressorSide, symbol, securityGroup12, securityType, securitySubType, maturityMonthYear, securityExchange4, maturityDate, unitOfMeasure, unitOfMeasureCurrency3, unitOfMeasureQtyOptional, couponRate, priceType, trdType, mdEntryId, putOrCall, strikePrice, restructuringType, seniority, referenceId100, strategyLinkId, legRefId, tradeBlocksUnderlyingsGroups, tradeBlocksPartyIdsGroups, tradeBlocksOriginalLegsGroups }, bytes)

theorem encode_length_pos (message : TradeBlocksLegacyGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksLegacyGroup) : (encode message).length ≤ 65362 := by
  have bound_tradeBlocksUnderlyingsGroups := TradeBlocksUnderlyingsGroups.encode_length_le message.tradeBlocksUnderlyingsGroups
  have bound_tradeBlocksPartyIdsGroups := TradeBlocksPartyIdsGroups.encode_length_le message.tradeBlocksPartyIdsGroups
  have bound_tradeBlocksOriginalLegsGroups := TradeBlocksOriginalLegsGroups.encode_length_le message.tradeBlocksOriginalLegsGroups
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, MdEntrySize.encode_length, Alpha.encode_length, MaturityMonthYear.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksLegacyGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntrySize.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksPartyIdsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksOriginalLegsGroups.decode_encode, Option.bind_some]
  rfl

end TradeBlocksLegacyGroup

/-- Trade Blocks Legacy Groups -/
structure TradeBlocksLegacyGroups where
  blockLength : BitVec 16
  tradeBlocksLegacyGroup : Bounded 1 TradeBlocksLegacyGroup
  deriving DecidableEq, Repr

namespace TradeBlocksLegacyGroups

def encode (message : TradeBlocksLegacyGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksLegacyGroup.val.length)
    ++ encodeMany TradeBlocksLegacyGroup.encode message.tradeBlocksLegacyGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksLegacyGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksLegacyGroup_, bytes) ← decodeMany TradeBlocksLegacyGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksLegacyGroup : tradeBlocksLegacyGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksLegacyGroup := ⟨tradeBlocksLegacyGroup_, fits_tradeBlocksLegacyGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksLegacyGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksLegacyGroups) : (encode message).length ≤ 16667313 := by
  have bound_tradeBlocksLegacyGroup := message.tradeBlocksLegacyGroup.length_lt
  have bound_tradeBlocksLegacyGroup_items := encodeMany_length_le TradeBlocksLegacyGroup.encode 65362 TradeBlocksLegacyGroup.encode_length_le message.tradeBlocksLegacyGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksLegacyGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksLegacyGroup.encode TradeBlocksLegacyGroup.decode TradeBlocksLegacyGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksLegacyGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksLegacyGroups

/-- Md Incremental Refresh Trade Blocks 349 -/
structure MdIncrementalRefreshTradeBlocks349 where
  transactTimeOptional : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessages : BitVec 16
  tradeDate : BitVec 16
  tradeBlocksLegacyGroups : TradeBlocksLegacyGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeBlocks349

def encode (message : MdIncrementalRefreshTradeBlocks349) : List UInt8 :=
  encodeUIntLE 8 message.transactTimeOptional
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessages
    ++ encodeUIntLE 2 message.tradeDate
    ++ TradeBlocksLegacyGroups.encode message.tradeBlocksLegacyGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeBlocks349 × List UInt8) := do
  let (transactTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessages, bytes) ← decodeUIntLE 2 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeBlocksLegacyGroups, bytes) ← TradeBlocksLegacyGroups.decode bytes
  pure ({ transactTimeOptional, matchEventIndicator, batchTotalMessages, tradeDate, tradeBlocksLegacyGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeBlocks349) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeBlocks349) : (encode message).length ≤ 16667326 := by
  have bound_tradeBlocksLegacyGroups := TradeBlocksLegacyGroups.encode_length_le message.tradeBlocksLegacyGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeBlocks349) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [TradeBlocksLegacyGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshTradeBlocks349

/-- Cal Fut Px: 9 bytes -/
structure CalFutPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace CalFutPx

def encode (message : CalFutPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (CalFutPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : CalFutPx) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CalFutPx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CalFutPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end CalFutPx

/-- Eris Original Group -/
structure ErisOriginalGroup where
  mdUpdateActionChar : Alpha 1
  mdEntryType : Alpha 1
  rptSeq : BitVec 32
  mdEntryPxDecimal : MdEntryPxDecimal
  mdEntrySizeOptional : BitVec 64
  calFutPx : CalFutPx
  mdEntryPositionNo : BitVec 32
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  symbol : Alpha 50
  securityGroup26 : Alpha 26
  securityType : Alpha 9
  securityExchange : Alpha 4
  productOptional : BitVec 8
  maturityDate : BitVec 16
  referenceId50 : Alpha 50
  erisSecurityAltIdGroups : ErisSecurityAltIdGroups
  eventsGroups : EventsGroups
  deriving DecidableEq, Repr

namespace ErisOriginalGroup

def encode (message : ErisOriginalGroup) : List UInt8 :=
  Alpha.encode message.mdUpdateActionChar
    ++ Alpha.encode message.mdEntryType
    ++ encodeUIntLE 4 message.rptSeq
    ++ MdEntryPxDecimal.encode message.mdEntryPxDecimal
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ CalFutPx.encode message.calFutPx
    ++ encodeUIntLE 4 message.mdEntryPositionNo
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup26
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ encodeUInt 1 message.productOptional
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.referenceId50
    ++ ErisSecurityAltIdGroups.encode message.erisSecurityAltIdGroups
    ++ EventsGroups.encode message.eventsGroups

def decode (bytes : List UInt8) : Option (ErisOriginalGroup × List UInt8) := do
  let (mdUpdateActionChar, bytes) ← Alpha.decode 1 bytes
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxDecimal, bytes) ← MdEntryPxDecimal.decode bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (calFutPx, bytes) ← CalFutPx.decode bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup26, bytes) ← Alpha.decode 26 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (referenceId50, bytes) ← Alpha.decode 50 bytes
  let (erisSecurityAltIdGroups, bytes) ← ErisSecurityAltIdGroups.decode bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  pure ({ mdUpdateActionChar, mdEntryType, rptSeq, mdEntryPxDecimal, mdEntrySizeOptional, calFutPx, mdEntryPositionNo, numberOfOrders, tradeId, aggressorSide, symbol, securityGroup26, securityType, securityExchange, productOptional, maturityDate, referenceId50, erisSecurityAltIdGroups, eventsGroups }, bytes)

theorem encode_length_pos (message : ErisOriginalGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisOriginalGroup) : (encode message).length ≤ 9373 := by
  have bound_erisSecurityAltIdGroups := ErisSecurityAltIdGroups.encode_length_le message.erisSecurityAltIdGroups
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, MdEntryPxDecimal.encode_length, CalFutPx.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisOriginalGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryPxDecimal.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [CalFutPx.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ErisSecurityAltIdGroups.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode, Option.bind_some]
  rfl

end ErisOriginalGroup

/-- Eris Original Groups -/
structure ErisOriginalGroups where
  blockLength : BitVec 16
  erisOriginalGroup : Bounded 1 ErisOriginalGroup
  deriving DecidableEq, Repr

namespace ErisOriginalGroups

def encode (message : ErisOriginalGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisOriginalGroup.val.length)
    ++ encodeMany ErisOriginalGroup.encode message.erisOriginalGroup.val

def decode (bytes : List UInt8) : Option (ErisOriginalGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisOriginalGroup_, bytes) ← decodeMany ErisOriginalGroup.decode numInGroup8.toNat bytes
  if fits_erisOriginalGroup : erisOriginalGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisOriginalGroup := ⟨erisOriginalGroup_, fits_erisOriginalGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisOriginalGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisOriginalGroups) : (encode message).length ≤ 2390118 := by
  have bound_erisOriginalGroup := message.erisOriginalGroup.length_lt
  have bound_erisOriginalGroup_items := encodeMany_length_le ErisOriginalGroup.encode 9373 ErisOriginalGroup.encode_length_le message.erisOriginalGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisOriginalGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisOriginalGroup.encode ErisOriginalGroup.decode ErisOriginalGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisOriginalGroup.length_lt, ↓reduceDIte]
  rfl

end ErisOriginalGroups

/-- Md Incremental Refresh Eris 351 -/
structure MdIncrementalRefreshEris351 where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  erisOriginalGroups : ErisOriginalGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshEris351

def encode (message : MdIncrementalRefreshEris351) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ ErisOriginalGroups.encode message.erisOriginalGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshEris351 × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (erisOriginalGroups, bytes) ← ErisOriginalGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, batchTotalMessagesOptional, erisOriginalGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshEris351) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshEris351) : (encode message).length ≤ 2390129 := by
  have bound_erisOriginalGroups := ErisOriginalGroups.encode_length_le message.erisOriginalGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshEris351) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ErisOriginalGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshEris351

/-- Eris Group -/
structure ErisGroup where
  mdUpdateActionChar : Alpha 1
  mdEntryType : Alpha 1
  rptSeq : BitVec 32
  mdEntryPxDecimal : MdEntryPxDecimal
  mdEntrySizeOptional : BitVec 64
  calFutPx : CalFutPx
  mdEntryPositionNo : BitVec 32
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  symbol : Alpha 50
  securityGroup26 : Alpha 26
  securityType : Alpha 9
  securityExchange : Alpha 4
  productOptional : BitVec 8
  maturityDate : BitVec 16
  referenceId50 : Alpha 50
  mdQuoteType : BitVec 8
  erisSecurityAltIdGroups : ErisSecurityAltIdGroups
  eventsGroups : EventsGroups
  deriving DecidableEq, Repr

namespace ErisGroup

def encode (message : ErisGroup) : List UInt8 :=
  Alpha.encode message.mdUpdateActionChar
    ++ Alpha.encode message.mdEntryType
    ++ encodeUIntLE 4 message.rptSeq
    ++ MdEntryPxDecimal.encode message.mdEntryPxDecimal
    ++ encodeUIntLE 8 message.mdEntrySizeOptional
    ++ CalFutPx.encode message.calFutPx
    ++ encodeUIntLE 4 message.mdEntryPositionNo
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup26
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ encodeUInt 1 message.productOptional
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.referenceId50
    ++ encodeUInt 1 message.mdQuoteType
    ++ ErisSecurityAltIdGroups.encode message.erisSecurityAltIdGroups
    ++ EventsGroups.encode message.eventsGroups

def decode (bytes : List UInt8) : Option (ErisGroup × List UInt8) := do
  let (mdUpdateActionChar, bytes) ← Alpha.decode 1 bytes
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxDecimal, bytes) ← MdEntryPxDecimal.decode bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (calFutPx, bytes) ← CalFutPx.decode bytes
  let (mdEntryPositionNo, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup26, bytes) ← Alpha.decode 26 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (referenceId50, bytes) ← Alpha.decode 50 bytes
  let (mdQuoteType, bytes) ← decodeUInt 1 bytes
  let (erisSecurityAltIdGroups, bytes) ← ErisSecurityAltIdGroups.decode bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  pure ({ mdUpdateActionChar, mdEntryType, rptSeq, mdEntryPxDecimal, mdEntrySizeOptional, calFutPx, mdEntryPositionNo, numberOfOrders, tradeId, aggressorSide, symbol, securityGroup26, securityType, securityExchange, productOptional, maturityDate, referenceId50, mdQuoteType, erisSecurityAltIdGroups, eventsGroups }, bytes)

theorem encode_length_pos (message : ErisGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisGroup) : (encode message).length ≤ 9374 := by
  have bound_erisSecurityAltIdGroups := ErisSecurityAltIdGroups.encode_length_le message.erisSecurityAltIdGroups
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, MdEntryPxDecimal.encode_length, CalFutPx.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntryPxDecimal.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [CalFutPx.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ErisSecurityAltIdGroups.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode, Option.bind_some]
  rfl

end ErisGroup

/-- Eris Groups -/
structure ErisGroups where
  blockLength : BitVec 16
  erisGroup : Bounded 1 ErisGroup
  deriving DecidableEq, Repr

namespace ErisGroups

def encode (message : ErisGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisGroup.val.length)
    ++ encodeMany ErisGroup.encode message.erisGroup.val

def decode (bytes : List UInt8) : Option (ErisGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisGroup_, bytes) ← decodeMany ErisGroup.decode numInGroup8.toNat bytes
  if fits_erisGroup : erisGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisGroup := ⟨erisGroup_, fits_erisGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisGroups) : (encode message).length ≤ 2390373 := by
  have bound_erisGroup := message.erisGroup.length_lt
  have bound_erisGroup_items := encodeMany_length_le ErisGroup.encode 9374 ErisGroup.encode_length_le message.erisGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisGroup.encode ErisGroup.decode ErisGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisGroup.length_lt, ↓reduceDIte]
  rfl

end ErisGroups

/-- Md Incremental Refresh Eris 353 -/
structure MdIncrementalRefreshEris353 where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  erisGroups : ErisGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshEris353

def encode (message : MdIncrementalRefreshEris353) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ ErisGroups.encode message.erisGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshEris353 × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (erisGroups, bytes) ← ErisGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, batchTotalMessagesOptional, erisGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshEris353) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshEris353) : (encode message).length ≤ 2390384 := by
  have bound_erisGroups := ErisGroups.encode_length_le message.erisGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshEris353) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ErisGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshEris353

/-- Strike Price Decimal: 9 bytes -/
structure StrikePriceDecimal where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceDecimal

def encode (message : StrikePriceDecimal) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (StrikePriceDecimal × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : StrikePriceDecimal) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceDecimal) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceDecimal) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end StrikePriceDecimal

/-- Unit Of Measure Qty Decimal: 9 bytes -/
structure UnitOfMeasureQtyDecimal where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace UnitOfMeasureQtyDecimal

def encode (message : UnitOfMeasureQtyDecimal) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (UnitOfMeasureQtyDecimal × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : UnitOfMeasureQtyDecimal) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UnitOfMeasureQtyDecimal) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnitOfMeasureQtyDecimal) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end UnitOfMeasureQtyDecimal

/-- Otc Underlyings Group: 68 bytes -/
structure OtcUnderlyingsGroup where
  underlyingSymbol : Alpha 50
  underlyingMaturityMonthYear : UnderlyingMaturityMonthYear
  underlyingSecurityType : Alpha 9
  underlyingSecurityExchangeSecurityExchange : Alpha 4
  deriving DecidableEq, Repr

namespace OtcUnderlyingsGroup

def encode (message : OtcUnderlyingsGroup) : List UInt8 :=
  Alpha.encode message.underlyingSymbol
    ++ UnderlyingMaturityMonthYear.encode message.underlyingMaturityMonthYear
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingSecurityExchangeSecurityExchange

def decode (bytes : List UInt8) : Option (OtcUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbol, bytes) ← Alpha.decode 50 bytes
  let (underlyingMaturityMonthYear, bytes) ← UnderlyingMaturityMonthYear.decode bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 9 bytes
  let (underlyingSecurityExchangeSecurityExchange, bytes) ← Alpha.decode 4 bytes
  pure ({ underlyingSymbol, underlyingMaturityMonthYear, underlyingSecurityType, underlyingSecurityExchangeSecurityExchange }, bytes)

@[simp] theorem encode_length (message : OtcUnderlyingsGroup) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, UnderlyingMaturityMonthYear.encode_length]

theorem encode_length_pos (message : OtcUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OtcUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [UnderlyingMaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OtcUnderlyingsGroup

/-- Otc Underlyings Groups -/
structure OtcUnderlyingsGroups where
  blockLength : BitVec 16
  otcUnderlyingsGroup : Bounded 1 OtcUnderlyingsGroup
  deriving DecidableEq, Repr

namespace OtcUnderlyingsGroups

def encode (message : OtcUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.otcUnderlyingsGroup.val.length)
    ++ encodeMany OtcUnderlyingsGroup.encode message.otcUnderlyingsGroup.val

def decode (bytes : List UInt8) : Option (OtcUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (otcUnderlyingsGroup_, bytes) ← decodeMany OtcUnderlyingsGroup.decode numInGroup8.toNat bytes
  if fits_otcUnderlyingsGroup : otcUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, otcUnderlyingsGroup := ⟨otcUnderlyingsGroup_, fits_otcUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OtcUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcUnderlyingsGroups) : (encode message).length ≤ 17343 := by
  have bound_otcUnderlyingsGroup := message.otcUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OtcUnderlyingsGroup.encode 68 OtcUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OtcUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OtcUnderlyingsGroup.encode OtcUnderlyingsGroup.decode OtcUnderlyingsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.otcUnderlyingsGroup.length_lt, ↓reduceDIte]
  rfl

end OtcUnderlyingsGroups

/-- Otc Security Alt Id Group: 51 bytes -/
structure OtcSecurityAltIdGroup where
  securityAltIDStringLength50 : Alpha 50
  securityAltIdSource : Alpha 1
  deriving DecidableEq, Repr

namespace OtcSecurityAltIdGroup

def encode (message : OtcSecurityAltIdGroup) : List UInt8 :=
  Alpha.encode message.securityAltIDStringLength50
    ++ Alpha.encode message.securityAltIdSource

def decode (bytes : List UInt8) : Option (OtcSecurityAltIdGroup × List UInt8) := do
  let (securityAltIDStringLength50, bytes) ← Alpha.decode 50 bytes
  let (securityAltIdSource, bytes) ← Alpha.decode 1 bytes
  pure ({ securityAltIDStringLength50, securityAltIdSource }, bytes)

@[simp] theorem encode_length (message : OtcSecurityAltIdGroup) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OtcSecurityAltIdGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OtcSecurityAltIdGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OtcSecurityAltIdGroup

/-- Otc Security Alt Id Groups -/
structure OtcSecurityAltIdGroups where
  blockLength : BitVec 16
  otcSecurityAltIdGroup : Bounded 1 OtcSecurityAltIdGroup
  deriving DecidableEq, Repr

namespace OtcSecurityAltIdGroups

def encode (message : OtcSecurityAltIdGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.otcSecurityAltIdGroup.val.length)
    ++ encodeMany OtcSecurityAltIdGroup.encode message.otcSecurityAltIdGroup.val

def decode (bytes : List UInt8) : Option (OtcSecurityAltIdGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (otcSecurityAltIdGroup_, bytes) ← decodeMany OtcSecurityAltIdGroup.decode numInGroup8.toNat bytes
  if fits_otcSecurityAltIdGroup : otcSecurityAltIdGroup_.length < 256 ^ 1 then
    pure ({ blockLength, otcSecurityAltIdGroup := ⟨otcSecurityAltIdGroup_, fits_otcSecurityAltIdGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OtcSecurityAltIdGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcSecurityAltIdGroups) : (encode message).length ≤ 13008 := by
  have bound_otcSecurityAltIdGroup := message.otcSecurityAltIdGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OtcSecurityAltIdGroup.encode 51 OtcSecurityAltIdGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OtcSecurityAltIdGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OtcSecurityAltIdGroup.encode OtcSecurityAltIdGroup.decode OtcSecurityAltIdGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.otcSecurityAltIdGroup.length_lt, ↓reduceDIte]
  rfl

end OtcSecurityAltIdGroups

/-- Otc Original Group -/
structure OtcOriginalGroup where
  mdEntryType : Alpha 1
  rptSeq : BitVec 32
  mdEntryPxOptional : BitVec 64
  mdEntrySize : MdEntrySize
  symbol : Alpha 50
  securityGroup12 : Alpha 12
  securityType : Alpha 9
  maturityMonthYear : MaturityMonthYear
  securityExchange : Alpha 4
  productOptional : BitVec 8
  maturityDate : BitVec 16
  couponRate : BitVec 32
  restructuringType : Alpha 2
  seniority : Alpha 2
  notionalPercentageOutstanding : BitVec 32
  putOrCall : BitVec 8
  strikePriceDecimal : StrikePriceDecimal
  unitOfMeasure : Alpha 5
  unitOfMeasureCurrency : Alpha 3
  unitOfMeasureQtyDecimal : UnitOfMeasureQtyDecimal
  mdEntryDate : BitVec 32
  openCloseSettlFlag : BitVec 8
  priceType : BitVec 16
  settlDate : BitVec 16
  quoteCondition : Alpha 1
  marketSector : Alpha 26
  sectorGroup : Alpha 2
  sectorSubGroup : Alpha 26
  productComplex : Alpha 26
  securitySubType : Alpha 2
  volType : BitVec 16
  referenceId100 : Alpha 100
  otcUnderlyingsGroups : OtcUnderlyingsGroups
  otcSecurityAltIdGroups : OtcSecurityAltIdGroups
  deriving DecidableEq, Repr

namespace OtcOriginalGroup

def encode (message : OtcOriginalGroup) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.mdEntryPxOptional
    ++ MdEntrySize.encode message.mdEntrySize
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup12
    ++ Alpha.encode message.securityType
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.securityExchange
    ++ encodeUInt 1 message.productOptional
    ++ encodeUIntLE 2 message.maturityDate
    ++ encodeUIntLE 4 message.couponRate
    ++ Alpha.encode message.restructuringType
    ++ Alpha.encode message.seniority
    ++ encodeUIntLE 4 message.notionalPercentageOutstanding
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePriceDecimal.encode message.strikePriceDecimal
    ++ Alpha.encode message.unitOfMeasure
    ++ Alpha.encode message.unitOfMeasureCurrency
    ++ UnitOfMeasureQtyDecimal.encode message.unitOfMeasureQtyDecimal
    ++ encodeUIntLE 4 message.mdEntryDate
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 2 message.priceType
    ++ encodeUIntLE 2 message.settlDate
    ++ Alpha.encode message.quoteCondition
    ++ Alpha.encode message.marketSector
    ++ Alpha.encode message.sectorGroup
    ++ Alpha.encode message.sectorSubGroup
    ++ Alpha.encode message.productComplex
    ++ Alpha.encode message.securitySubType
    ++ encodeUIntLE 2 message.volType
    ++ Alpha.encode message.referenceId100
    ++ OtcUnderlyingsGroups.encode message.otcUnderlyingsGroups
    ++ OtcSecurityAltIdGroups.encode message.otcSecurityAltIdGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OtcOriginalGroup × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← MdEntrySize.decode bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (restructuringType, bytes) ← Alpha.decode 2 bytes
  let (seniority, bytes) ← Alpha.decode 2 bytes
  let (notionalPercentageOutstanding, bytes) ← decodeUIntLE 4 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePriceDecimal, bytes) ← StrikePriceDecimal.decode bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureCurrency, bytes) ← Alpha.decode 3 bytes
  let (unitOfMeasureQtyDecimal, bytes) ← UnitOfMeasureQtyDecimal.decode bytes
  let (mdEntryDate, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (priceType, bytes) ← decodeUIntLE 2 bytes
  let (settlDate, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← Alpha.decode 1 bytes
  let (marketSector, bytes) ← Alpha.decode 26 bytes
  let (sectorGroup, bytes) ← Alpha.decode 2 bytes
  let (sectorSubGroup, bytes) ← Alpha.decode 26 bytes
  let (productComplex, bytes) ← Alpha.decode 26 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (volType, bytes) ← decodeUIntLE 2 bytes
  let (referenceId100, bytes) ← Alpha.decode 100 bytes
  let (otcUnderlyingsGroups, bytes) ← OtcUnderlyingsGroups.decode bytes
  let (otcSecurityAltIdGroups, bytes) ← OtcSecurityAltIdGroups.decode bytes
  pure ({ mdEntryType, rptSeq, mdEntryPxOptional, mdEntrySize, symbol, securityGroup12, securityType, maturityMonthYear, securityExchange, productOptional, maturityDate, couponRate, restructuringType, seniority, notionalPercentageOutstanding, putOrCall, strikePriceDecimal, unitOfMeasure, unitOfMeasureCurrency, unitOfMeasureQtyDecimal, mdEntryDate, openCloseSettlFlag, priceType, settlDate, quoteCondition, marketSector, sectorGroup, sectorSubGroup, productComplex, securitySubType, volType, referenceId100, otcUnderlyingsGroups, otcSecurityAltIdGroups }, bytes)

theorem encode_length_pos (message : OtcOriginalGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcOriginalGroup) : (encode message).length ≤ 30689 := by
  have bound_otcUnderlyingsGroups := OtcUnderlyingsGroups.encode_length_le message.otcUnderlyingsGroups
  have bound_otcSecurityAltIdGroups := OtcSecurityAltIdGroups.encode_length_le message.otcSecurityAltIdGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, MdEntrySize.encode_length, MaturityMonthYear.encode_length, encodeUInt_length, StrikePriceDecimal.encode_length, UnitOfMeasureQtyDecimal.encode_length]
  omega

@[simp] theorem decode_encode (message : OtcOriginalGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntrySize.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [StrikePriceDecimal.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [UnitOfMeasureQtyDecimal.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OtcUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OtcSecurityAltIdGroups.decode_encode, Option.bind_some]
  rfl

end OtcOriginalGroup

/-- Otc Original Groups -/
structure OtcOriginalGroups where
  blockLength : BitVec 16
  otcOriginalGroup : Bounded 1 OtcOriginalGroup
  deriving DecidableEq, Repr

namespace OtcOriginalGroups

def encode (message : OtcOriginalGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.otcOriginalGroup.val.length)
    ++ encodeMany OtcOriginalGroup.encode message.otcOriginalGroup.val

def decode (bytes : List UInt8) : Option (OtcOriginalGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (otcOriginalGroup_, bytes) ← decodeMany OtcOriginalGroup.decode numInGroup8.toNat bytes
  if fits_otcOriginalGroup : otcOriginalGroup_.length < 256 ^ 1 then
    pure ({ blockLength, otcOriginalGroup := ⟨otcOriginalGroup_, fits_otcOriginalGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OtcOriginalGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcOriginalGroups) : (encode message).length ≤ 7825698 := by
  have bound_otcOriginalGroup := message.otcOriginalGroup.length_lt
  have bound_otcOriginalGroup_items := encodeMany_length_le OtcOriginalGroup.encode 30689 OtcOriginalGroup.encode_length_le message.otcOriginalGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : OtcOriginalGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OtcOriginalGroup.encode OtcOriginalGroup.decode OtcOriginalGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.otcOriginalGroup.length_lt, ↓reduceDIte]
  rfl

end OtcOriginalGroups

/-- Md Incremental Refresh Ot C 356 -/
structure MdIncrementalRefreshOtC356 where
  transactTime : BitVec 64
  tradeDate : BitVec 16
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  otcOriginalGroups : OtcOriginalGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshOtC356

def encode (message : MdIncrementalRefreshOtC356) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ OtcOriginalGroups.encode message.otcOriginalGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshOtC356 × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (otcOriginalGroups, bytes) ← OtcOriginalGroups.decode bytes
  pure ({ transactTime, tradeDate, matchEventIndicator, batchTotalMessagesOptional, otcOriginalGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshOtC356) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshOtC356) : (encode message).length ≤ 7825711 := by
  have bound_otcOriginalGroups := OtcOriginalGroups.encode_length_le message.otcOriginalGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshOtC356) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OtcOriginalGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshOtC356

/-- Min Price Increment: 9 bytes -/
structure MinPriceIncrement where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MinPriceIncrement

def encode (message : MinPriceIncrement) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MinPriceIncrement × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MinPriceIncrement) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MinPriceIncrement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinPriceIncrement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MinPriceIncrement

/-- Eris Feed Types Group: 4 bytes -/
structure ErisFeedTypesGroup where
  mdFeedType3 : Alpha 3
  marketDepth : BitVec 8
  deriving DecidableEq, Repr

namespace ErisFeedTypesGroup

def encode (message : ErisFeedTypesGroup) : List UInt8 :=
  Alpha.encode message.mdFeedType3
    ++ encodeUInt 1 message.marketDepth

def decode (bytes : List UInt8) : Option (ErisFeedTypesGroup × List UInt8) := do
  let (mdFeedType3, bytes) ← Alpha.decode 3 bytes
  let (marketDepth, bytes) ← decodeUInt 1 bytes
  pure ({ mdFeedType3, marketDepth }, bytes)

@[simp] theorem encode_length (message : ErisFeedTypesGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ErisFeedTypesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErisFeedTypesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ErisFeedTypesGroup

/-- Eris Feed Types Groups -/
structure ErisFeedTypesGroups where
  blockLength : BitVec 16
  erisFeedTypesGroup : Bounded 1 ErisFeedTypesGroup
  deriving DecidableEq, Repr

namespace ErisFeedTypesGroups

def encode (message : ErisFeedTypesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisFeedTypesGroup.val.length)
    ++ encodeMany ErisFeedTypesGroup.encode message.erisFeedTypesGroup.val

def decode (bytes : List UInt8) : Option (ErisFeedTypesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisFeedTypesGroup_, bytes) ← decodeMany ErisFeedTypesGroup.decode numInGroup8.toNat bytes
  if fits_erisFeedTypesGroup : erisFeedTypesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisFeedTypesGroup := ⟨erisFeedTypesGroup_, fits_erisFeedTypesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisFeedTypesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisFeedTypesGroups) : (encode message).length ≤ 1023 := by
  have bound_erisFeedTypesGroup := message.erisFeedTypesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const ErisFeedTypesGroup.encode 4 ErisFeedTypesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ErisFeedTypesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisFeedTypesGroup.encode ErisFeedTypesGroup.decode ErisFeedTypesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisFeedTypesGroup.length_lt, ↓reduceDIte]
  rfl

end ErisFeedTypesGroups

/-- Previous Fixing Rate: 9 bytes -/
structure PreviousFixingRate where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousFixingRate

def encode (message : PreviousFixingRate) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (PreviousFixingRate × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : PreviousFixingRate) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousFixingRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousFixingRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end PreviousFixingRate

/-- Interpolation Factor: 9 bytes -/
structure InterpolationFactor where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace InterpolationFactor

def encode (message : InterpolationFactor) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (InterpolationFactor × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : InterpolationFactor) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : InterpolationFactor) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InterpolationFactor) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end InterpolationFactor

/-- Eris Legs Group -/
structure ErisLegsGroup where
  legBenchmarkCurveName : Alpha 5
  rateDescriptor : Alpha 8
  previousFixingDate : BitVec 16
  legPayFrequencey : Alpha 3
  previousFixingRate : PreviousFixingRate
  legSymbol : Alpha 50
  legRatioQtyInt32Null : BitVec 32
  legSide : BitVec 8
  legCurrency : Alpha 3
  legSecurityType4 : Alpha 8
  legSecurityGroup : Alpha 12
  legDateOffset : BitVec 8
  interpolationFactor : InterpolationFactor
  erisSecurityAltIdGroups : ErisSecurityAltIdGroups
  deriving DecidableEq, Repr

namespace ErisLegsGroup

def encode (message : ErisLegsGroup) : List UInt8 :=
  Alpha.encode message.legBenchmarkCurveName
    ++ Alpha.encode message.rateDescriptor
    ++ encodeUIntLE 2 message.previousFixingDate
    ++ Alpha.encode message.legPayFrequencey
    ++ PreviousFixingRate.encode message.previousFixingRate
    ++ Alpha.encode message.legSymbol
    ++ encodeUIntLE 4 message.legRatioQtyInt32Null
    ++ encodeUInt 1 message.legSide
    ++ Alpha.encode message.legCurrency
    ++ Alpha.encode message.legSecurityType4
    ++ Alpha.encode message.legSecurityGroup
    ++ encodeUInt 1 message.legDateOffset
    ++ InterpolationFactor.encode message.interpolationFactor
    ++ ErisSecurityAltIdGroups.encode message.erisSecurityAltIdGroups

def decode (bytes : List UInt8) : Option (ErisLegsGroup × List UInt8) := do
  let (legBenchmarkCurveName, bytes) ← Alpha.decode 5 bytes
  let (rateDescriptor, bytes) ← Alpha.decode 8 bytes
  let (previousFixingDate, bytes) ← decodeUIntLE 2 bytes
  let (legPayFrequencey, bytes) ← Alpha.decode 3 bytes
  let (previousFixingRate, bytes) ← PreviousFixingRate.decode bytes
  let (legSymbol, bytes) ← Alpha.decode 50 bytes
  let (legRatioQtyInt32Null, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legCurrency, bytes) ← Alpha.decode 3 bytes
  let (legSecurityType4, bytes) ← Alpha.decode 8 bytes
  let (legSecurityGroup, bytes) ← Alpha.decode 12 bytes
  let (legDateOffset, bytes) ← decodeUInt 1 bytes
  let (interpolationFactor, bytes) ← InterpolationFactor.decode bytes
  let (erisSecurityAltIdGroups, bytes) ← ErisSecurityAltIdGroups.decode bytes
  pure ({ legBenchmarkCurveName, rateDescriptor, previousFixingDate, legPayFrequencey, previousFixingRate, legSymbol, legRatioQtyInt32Null, legSide, legCurrency, legSecurityType4, legSecurityGroup, legDateOffset, interpolationFactor, erisSecurityAltIdGroups }, bytes)

theorem encode_length_pos (message : ErisLegsGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisLegsGroup) : (encode message).length ≤ 7003 := by
  have bound_erisSecurityAltIdGroups := ErisSecurityAltIdGroups.encode_length_le message.erisSecurityAltIdGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, PreviousFixingRate.encode_length, encodeUInt_length, InterpolationFactor.encode_length]
  omega

@[simp] theorem decode_encode (message : ErisLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PreviousFixingRate.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [InterpolationFactor.decode_encode]
  simp only [Option.bind_some]
  rw [ErisSecurityAltIdGroups.decode_encode, Option.bind_some]
  rfl

end ErisLegsGroup

/-- Eris Legs Groups -/
structure ErisLegsGroups where
  blockLength : BitVec 16
  erisLegsGroup : Bounded 1 ErisLegsGroup
  deriving DecidableEq, Repr

namespace ErisLegsGroups

def encode (message : ErisLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.erisLegsGroup.val.length)
    ++ encodeMany ErisLegsGroup.encode message.erisLegsGroup.val

def decode (bytes : List UInt8) : Option (ErisLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (erisLegsGroup_, bytes) ← decodeMany ErisLegsGroup.decode numInGroup8.toNat bytes
  if fits_erisLegsGroup : erisLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, erisLegsGroup := ⟨erisLegsGroup_, fits_erisLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ErisLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ErisLegsGroups) : (encode message).length ≤ 1785768 := by
  have bound_erisLegsGroup := message.erisLegsGroup.length_lt
  have bound_erisLegsGroup_items := encodeMany_length_le ErisLegsGroup.encode 7003 ErisLegsGroup.encode_length_le message.erisLegsGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ErisLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ErisLegsGroup.encode ErisLegsGroup.decode ErisLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.erisLegsGroup.length_lt, ↓reduceDIte]
  rfl

end ErisLegsGroups

/-- Md Instrument Definition Eris -/
structure MdInstrumentDefinitionEris where
  securityGroup12 : Alpha 12
  symbol : Alpha 50
  securityType4 : Alpha 4
  productOptional : BitVec 8
  securityExchange : Alpha 4
  maturityDate : BitVec 16
  currency : Alpha 3
  minPriceIncrement : MinPriceIncrement
  securityUpdateAction : SecurityUpdateAction
  rateType : Alpha 2
  couponRate : BitVec 32
  userDefinedInstrument : Alpha 1
  applId : BitVec 16
  erisFeedTypesGroups : ErisFeedTypesGroups
  eventsGroups : EventsGroups
  erisSecurityAltIdGroups : ErisSecurityAltIdGroups
  erisLegsGroups : ErisLegsGroups
  deriving DecidableEq, Repr

namespace MdInstrumentDefinitionEris

def encode (message : MdInstrumentDefinitionEris) : List UInt8 :=
  Alpha.encode message.securityGroup12
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityType4
    ++ encodeUInt 1 message.productOptional
    ++ Alpha.encode message.securityExchange
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.currency
    ++ MinPriceIncrement.encode message.minPriceIncrement
    ++ SecurityUpdateAction.encode message.securityUpdateAction
    ++ Alpha.encode message.rateType
    ++ encodeUIntLE 4 message.couponRate
    ++ Alpha.encode message.userDefinedInstrument
    ++ encodeUIntLE 2 message.applId
    ++ ErisFeedTypesGroups.encode message.erisFeedTypesGroups
    ++ EventsGroups.encode message.eventsGroups
    ++ ErisSecurityAltIdGroups.encode message.erisSecurityAltIdGroups
    ++ ErisLegsGroups.encode message.erisLegsGroups

def decode (bytes : List UInt8) : Option (MdInstrumentDefinitionEris × List UInt8) := do
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityType4, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (minPriceIncrement, bytes) ← MinPriceIncrement.decode bytes
  let (securityUpdateAction, bytes) ← SecurityUpdateAction.decode bytes
  let (rateType, bytes) ← Alpha.decode 2 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (userDefinedInstrument, bytes) ← Alpha.decode 1 bytes
  let (applId, bytes) ← decodeUIntLE 2 bytes
  let (erisFeedTypesGroups, bytes) ← ErisFeedTypesGroups.decode bytes
  let (eventsGroups, bytes) ← EventsGroups.decode bytes
  let (erisSecurityAltIdGroups, bytes) ← ErisSecurityAltIdGroups.decode bytes
  let (erisLegsGroups, bytes) ← ErisLegsGroups.decode bytes
  pure ({ securityGroup12, symbol, securityType4, productOptional, securityExchange, maturityDate, currency, minPriceIncrement, securityUpdateAction, rateType, couponRate, userDefinedInstrument, applId, erisFeedTypesGroups, eventsGroups, erisSecurityAltIdGroups, erisLegsGroups }, bytes)

theorem encode_length_pos (message : MdInstrumentDefinitionEris) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdInstrumentDefinitionEris) : (encode message).length ≤ 1796072 := by
  have bound_erisFeedTypesGroups := ErisFeedTypesGroups.encode_length_le message.erisFeedTypesGroups
  have bound_eventsGroups := EventsGroups.encode_length_le message.eventsGroups
  have bound_erisSecurityAltIdGroups := ErisSecurityAltIdGroups.encode_length_le message.erisSecurityAltIdGroups
  have bound_erisLegsGroups := ErisLegsGroups.encode_length_le message.erisLegsGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length, MinPriceIncrement.encode_length, SecurityUpdateAction.encode_length]
  omega

@[simp] theorem decode_encode (message : MdInstrumentDefinitionEris) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MinPriceIncrement.decode_encode]
  simp only [Option.bind_some]
  rw [SecurityUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ErisFeedTypesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [EventsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [ErisSecurityAltIdGroups.decode_encode]
  simp only [Option.bind_some]
  rw [ErisLegsGroups.decode_encode, Option.bind_some]
  rfl

end MdInstrumentDefinitionEris

/-- Unit Of Measure Qty Decimal Optional: 9 bytes -/
structure UnitOfMeasureQtyDecimalOptional where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace UnitOfMeasureQtyDecimalOptional

def encode (message : UnitOfMeasureQtyDecimalOptional) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (UnitOfMeasureQtyDecimalOptional × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : UnitOfMeasureQtyDecimalOptional) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UnitOfMeasureQtyDecimalOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnitOfMeasureQtyDecimalOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end UnitOfMeasureQtyDecimalOptional

/-- Strike Price Decimal Optional: 9 bytes -/
structure StrikePriceDecimalOptional where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceDecimalOptional

def encode (message : StrikePriceDecimalOptional) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (StrikePriceDecimalOptional × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : StrikePriceDecimalOptional) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceDecimalOptional) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceDecimalOptional) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end StrikePriceDecimalOptional

/-- Leg Strike Price Decimal 64 Null: 9 bytes -/
structure LegStrikePriceDecimal64Null where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LegStrikePriceDecimal64Null

def encode (message : LegStrikePriceDecimal64Null) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LegStrikePriceDecimal64Null × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : LegStrikePriceDecimal64Null) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegStrikePriceDecimal64Null) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegStrikePriceDecimal64Null) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegStrikePriceDecimal64Null

/-- Leg Unit Of Measure Qty Decimal 64 Null: 9 bytes -/
structure LegUnitOfMeasureQtyDecimal64Null where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LegUnitOfMeasureQtyDecimal64Null

def encode (message : LegUnitOfMeasureQtyDecimal64Null) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LegUnitOfMeasureQtyDecimal64Null × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : LegUnitOfMeasureQtyDecimal64Null) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegUnitOfMeasureQtyDecimal64Null) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegUnitOfMeasureQtyDecimal64Null) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegUnitOfMeasureQtyDecimal64Null

/-- Trade Blocks Legs Group: 137 bytes -/
structure TradeBlocksLegsGroup where
  legSymbol : Alpha 50
  legSecurityId : BitVec 64
  legSecurityGroup : Alpha 12
  legId : Alpha 17
  legSecurityType : Alpha 9
  legMaturityMonthYear : LegMaturityMonthYear
  legMaturityDate : BitVec 16
  legStrikePriceDecimal64Null : LegStrikePriceDecimal64Null
  legUnitOfMeasure : Alpha 5
  legUnitOfMeasureQtyDecimal64Null : LegUnitOfMeasureQtyDecimal64Null
  legSecurityExchange : Alpha 4
  legRatioQtyUInt16Null : BitVec 16
  legSide : BitVec 8
  legPutOrCall : BitVec 8
  legUnitOfMeasureCurrency : Alpha 3
  deriving DecidableEq, Repr

namespace TradeBlocksLegsGroup

def encode (message : TradeBlocksLegsGroup) : List UInt8 :=
  Alpha.encode message.legSymbol
    ++ encodeUIntLE 8 message.legSecurityId
    ++ Alpha.encode message.legSecurityGroup
    ++ Alpha.encode message.legId
    ++ Alpha.encode message.legSecurityType
    ++ LegMaturityMonthYear.encode message.legMaturityMonthYear
    ++ encodeUIntLE 2 message.legMaturityDate
    ++ LegStrikePriceDecimal64Null.encode message.legStrikePriceDecimal64Null
    ++ Alpha.encode message.legUnitOfMeasure
    ++ LegUnitOfMeasureQtyDecimal64Null.encode message.legUnitOfMeasureQtyDecimal64Null
    ++ Alpha.encode message.legSecurityExchange
    ++ encodeUIntLE 2 message.legRatioQtyUInt16Null
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legPutOrCall
    ++ Alpha.encode message.legUnitOfMeasureCurrency

def decode (bytes : List UInt8) : Option (TradeBlocksLegsGroup × List UInt8) := do
  let (legSymbol, bytes) ← Alpha.decode 50 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityGroup, bytes) ← Alpha.decode 12 bytes
  let (legId, bytes) ← Alpha.decode 17 bytes
  let (legSecurityType, bytes) ← Alpha.decode 9 bytes
  let (legMaturityMonthYear, bytes) ← LegMaturityMonthYear.decode bytes
  let (legMaturityDate, bytes) ← decodeUIntLE 2 bytes
  let (legStrikePriceDecimal64Null, bytes) ← LegStrikePriceDecimal64Null.decode bytes
  let (legUnitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (legUnitOfMeasureQtyDecimal64Null, bytes) ← LegUnitOfMeasureQtyDecimal64Null.decode bytes
  let (legSecurityExchange, bytes) ← Alpha.decode 4 bytes
  let (legRatioQtyUInt16Null, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legPutOrCall, bytes) ← decodeUInt 1 bytes
  let (legUnitOfMeasureCurrency, bytes) ← Alpha.decode 3 bytes
  pure ({ legSymbol, legSecurityId, legSecurityGroup, legId, legSecurityType, legMaturityMonthYear, legMaturityDate, legStrikePriceDecimal64Null, legUnitOfMeasure, legUnitOfMeasureQtyDecimal64Null, legSecurityExchange, legRatioQtyUInt16Null, legSide, legPutOrCall, legUnitOfMeasureCurrency }, bytes)

@[simp] theorem encode_length (message : TradeBlocksLegsGroup) : (encode message).length = 137 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, LegMaturityMonthYear.encode_length, LegStrikePriceDecimal64Null.encode_length, LegUnitOfMeasureQtyDecimal64Null.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBlocksLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBlocksLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [LegMaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [LegStrikePriceDecimal64Null.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [LegUnitOfMeasureQtyDecimal64Null.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeBlocksLegsGroup

/-- Trade Blocks Legs Groups -/
structure TradeBlocksLegsGroups where
  blockLength : BitVec 16
  tradeBlocksLegsGroup : Bounded 1 TradeBlocksLegsGroup
  deriving DecidableEq, Repr

namespace TradeBlocksLegsGroups

def encode (message : TradeBlocksLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksLegsGroup.val.length)
    ++ encodeMany TradeBlocksLegsGroup.encode message.tradeBlocksLegsGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksLegsGroup_, bytes) ← decodeMany TradeBlocksLegsGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksLegsGroup : tradeBlocksLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksLegsGroup := ⟨tradeBlocksLegsGroup_, fits_tradeBlocksLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksLegsGroups) : (encode message).length ≤ 34938 := by
  have bound_tradeBlocksLegsGroup := message.tradeBlocksLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeBlocksLegsGroup.encode 137 TradeBlocksLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksLegsGroup.encode TradeBlocksLegsGroup.decode TradeBlocksLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksLegsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksLegsGroups

/-- Trade Blocks Group -/
structure TradeBlocksGroup where
  mdUpdateAction : BitVec 8
  securityId : BitVec 64
  rptSeq : BitVec 32
  mdEntryPx : BitVec 64
  mdEntrySize : MdEntrySize
  numberOfOrders : BitVec 32
  tradeId : BitVec 32
  aggressorSide : BitVec 8
  symbol : Alpha 50
  securityGroup12 : Alpha 12
  securityType : Alpha 9
  securitySubType : Alpha 2
  maturityMonthYear : MaturityMonthYear
  securityExchange4 : Alpha 4
  maturityDate : BitVec 16
  unitOfMeasure : Alpha 5
  unitOfMeasureCurrency3 : Alpha 3
  unitOfMeasureQtyDecimalOptional : UnitOfMeasureQtyDecimalOptional
  couponRate : BitVec 32
  priceType : BitVec 16
  trdType : BitVec 8
  mdEntryId : Alpha 26
  putOrCall : BitVec 8
  strikePriceDecimalOptional : StrikePriceDecimalOptional
  restructuringType : Alpha 2
  seniority : Alpha 2
  referenceId100 : Alpha 100
  strategyLinkId : Alpha 26
  legRefId : Alpha 17
  tradeBlocksUnderlyingsGroups : TradeBlocksUnderlyingsGroups
  tradeBlocksPartyIdsGroups : TradeBlocksPartyIdsGroups
  tradeBlocksLegsGroups : TradeBlocksLegsGroups
  deriving DecidableEq, Repr

namespace TradeBlocksGroup

def encode (message : TradeBlocksGroup) : List UInt8 :=
  encodeUInt 1 message.mdUpdateAction
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ MdEntrySize.encode message.mdEntrySize
    ++ encodeUIntLE 4 message.numberOfOrders
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUInt 1 message.aggressorSide
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup12
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securitySubType
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.securityExchange4
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.unitOfMeasure
    ++ Alpha.encode message.unitOfMeasureCurrency3
    ++ UnitOfMeasureQtyDecimalOptional.encode message.unitOfMeasureQtyDecimalOptional
    ++ encodeUIntLE 4 message.couponRate
    ++ encodeUIntLE 2 message.priceType
    ++ encodeUInt 1 message.trdType
    ++ Alpha.encode message.mdEntryId
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePriceDecimalOptional.encode message.strikePriceDecimalOptional
    ++ Alpha.encode message.restructuringType
    ++ Alpha.encode message.seniority
    ++ Alpha.encode message.referenceId100
    ++ Alpha.encode message.strategyLinkId
    ++ Alpha.encode message.legRefId
    ++ TradeBlocksUnderlyingsGroups.encode message.tradeBlocksUnderlyingsGroups
    ++ TradeBlocksPartyIdsGroups.encode message.tradeBlocksPartyIdsGroups
    ++ TradeBlocksLegsGroups.encode message.tradeBlocksLegsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBlocksGroup × List UInt8) := do
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← MdEntrySize.decode bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (securityExchange4, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureCurrency3, bytes) ← Alpha.decode 3 bytes
  let (unitOfMeasureQtyDecimalOptional, bytes) ← UnitOfMeasureQtyDecimalOptional.decode bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (priceType, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUInt 1 bytes
  let (mdEntryId, bytes) ← Alpha.decode 26 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePriceDecimalOptional, bytes) ← StrikePriceDecimalOptional.decode bytes
  let (restructuringType, bytes) ← Alpha.decode 2 bytes
  let (seniority, bytes) ← Alpha.decode 2 bytes
  let (referenceId100, bytes) ← Alpha.decode 100 bytes
  let (strategyLinkId, bytes) ← Alpha.decode 26 bytes
  let (legRefId, bytes) ← Alpha.decode 17 bytes
  let (tradeBlocksUnderlyingsGroups, bytes) ← TradeBlocksUnderlyingsGroups.decode bytes
  let (tradeBlocksPartyIdsGroups, bytes) ← TradeBlocksPartyIdsGroups.decode bytes
  let (tradeBlocksLegsGroups, bytes) ← TradeBlocksLegsGroups.decode bytes
  pure ({ mdUpdateAction, securityId, rptSeq, mdEntryPx, mdEntrySize, numberOfOrders, tradeId, aggressorSide, symbol, securityGroup12, securityType, securitySubType, maturityMonthYear, securityExchange4, maturityDate, unitOfMeasure, unitOfMeasureCurrency3, unitOfMeasureQtyDecimalOptional, couponRate, priceType, trdType, mdEntryId, putOrCall, strikePriceDecimalOptional, restructuringType, seniority, referenceId100, strategyLinkId, legRefId, tradeBlocksUnderlyingsGroups, tradeBlocksPartyIdsGroups, tradeBlocksLegsGroups }, bytes)

theorem encode_length_pos (message : TradeBlocksGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksGroup) : (encode message).length ≤ 65874 := by
  have bound_tradeBlocksUnderlyingsGroups := TradeBlocksUnderlyingsGroups.encode_length_le message.tradeBlocksUnderlyingsGroups
  have bound_tradeBlocksPartyIdsGroups := TradeBlocksPartyIdsGroups.encode_length_le message.tradeBlocksPartyIdsGroups
  have bound_tradeBlocksLegsGroups := TradeBlocksLegsGroups.encode_length_le message.tradeBlocksLegsGroups
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, MdEntrySize.encode_length, Alpha.encode_length, MaturityMonthYear.encode_length, UnitOfMeasureQtyDecimalOptional.encode_length, StrikePriceDecimalOptional.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntrySize.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [UnitOfMeasureQtyDecimalOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [StrikePriceDecimalOptional.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksPartyIdsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeBlocksLegsGroups.decode_encode, Option.bind_some]
  rfl

end TradeBlocksGroup

/-- Trade Blocks Groups -/
structure TradeBlocksGroups where
  blockLength : BitVec 16
  tradeBlocksGroup : Bounded 1 TradeBlocksGroup
  deriving DecidableEq, Repr

namespace TradeBlocksGroups

def encode (message : TradeBlocksGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBlocksGroup.val.length)
    ++ encodeMany TradeBlocksGroup.encode message.tradeBlocksGroup.val

def decode (bytes : List UInt8) : Option (TradeBlocksGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (tradeBlocksGroup_, bytes) ← decodeMany TradeBlocksGroup.decode numInGroup8.toNat bytes
  if fits_tradeBlocksGroup : tradeBlocksGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBlocksGroup := ⟨tradeBlocksGroup_, fits_tradeBlocksGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBlocksGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBlocksGroups) : (encode message).length ≤ 16797873 := by
  have bound_tradeBlocksGroup := message.tradeBlocksGroup.length_lt
  have bound_tradeBlocksGroup_items := encodeMany_length_le TradeBlocksGroup.encode 65874 TradeBlocksGroup.encode_length_le message.tradeBlocksGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : TradeBlocksGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeBlocksGroup.encode TradeBlocksGroup.decode TradeBlocksGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeBlocksGroup.length_lt, ↓reduceDIte]
  rfl

end TradeBlocksGroups

/-- Md Incremental Refresh Trade Blocks 365 -/
structure MdIncrementalRefreshTradeBlocks365 where
  transactTimeOptional : BitVec 64
  matchEventIndicator : BitVec 8
  batchTotalMessages : BitVec 16
  tradeDate : BitVec 16
  tradeBlocksGroups : TradeBlocksGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTradeBlocks365

def encode (message : MdIncrementalRefreshTradeBlocks365) : List UInt8 :=
  encodeUIntLE 8 message.transactTimeOptional
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessages
    ++ encodeUIntLE 2 message.tradeDate
    ++ TradeBlocksGroups.encode message.tradeBlocksGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTradeBlocks365 × List UInt8) := do
  let (transactTimeOptional, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessages, bytes) ← decodeUIntLE 2 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (tradeBlocksGroups, bytes) ← TradeBlocksGroups.decode bytes
  pure ({ transactTimeOptional, matchEventIndicator, batchTotalMessages, tradeDate, tradeBlocksGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTradeBlocks365) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTradeBlocks365) : (encode message).length ≤ 16797886 := by
  have bound_tradeBlocksGroups := TradeBlocksGroups.encode_length_le message.tradeBlocksGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTradeBlocks365) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [TradeBlocksGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshTradeBlocks365

/-- Otc Group -/
structure OtcGroup where
  mdEntryType : Alpha 1
  rptSeq : BitVec 32
  mdEntryPx : BitVec 64
  mdEntrySize : MdEntrySize
  symbol : Alpha 50
  securityGroup12 : Alpha 12
  securityType : Alpha 9
  maturityMonthYear : MaturityMonthYear
  securityExchange : Alpha 4
  productOptional : BitVec 8
  maturityDate : BitVec 16
  couponRate : BitVec 32
  restructuringType : Alpha 2
  seniority : Alpha 2
  notionalPercentageOutstanding : BitVec 32
  putOrCall : BitVec 8
  strikePriceDecimalOptional : StrikePriceDecimalOptional
  unitOfMeasure : Alpha 5
  unitOfMeasureCurrency : Alpha 3
  unitOfMeasureQtyDecimalOptional : UnitOfMeasureQtyDecimalOptional
  mdEntryDate : BitVec 32
  openCloseSettlFlag : BitVec 8
  priceType : BitVec 16
  settlDate : BitVec 16
  quoteCondition : Alpha 1
  marketSector : Alpha 26
  sectorGroup : Alpha 2
  sectorSubGroup : Alpha 26
  productComplex : Alpha 26
  securitySubType : Alpha 2
  volType : BitVec 16
  referenceId100 : Alpha 100
  otcUnderlyingsGroups : OtcUnderlyingsGroups
  otcSecurityAltIdGroups : OtcSecurityAltIdGroups
  deriving DecidableEq, Repr

namespace OtcGroup

def encode (message : OtcGroup) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ encodeUIntLE 4 message.rptSeq
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ MdEntrySize.encode message.mdEntrySize
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.securityGroup12
    ++ Alpha.encode message.securityType
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ Alpha.encode message.securityExchange
    ++ encodeUInt 1 message.productOptional
    ++ encodeUIntLE 2 message.maturityDate
    ++ encodeUIntLE 4 message.couponRate
    ++ Alpha.encode message.restructuringType
    ++ Alpha.encode message.seniority
    ++ encodeUIntLE 4 message.notionalPercentageOutstanding
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePriceDecimalOptional.encode message.strikePriceDecimalOptional
    ++ Alpha.encode message.unitOfMeasure
    ++ Alpha.encode message.unitOfMeasureCurrency
    ++ UnitOfMeasureQtyDecimalOptional.encode message.unitOfMeasureQtyDecimalOptional
    ++ encodeUIntLE 4 message.mdEntryDate
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 2 message.priceType
    ++ encodeUIntLE 2 message.settlDate
    ++ Alpha.encode message.quoteCondition
    ++ Alpha.encode message.marketSector
    ++ Alpha.encode message.sectorGroup
    ++ Alpha.encode message.sectorSubGroup
    ++ Alpha.encode message.productComplex
    ++ Alpha.encode message.securitySubType
    ++ encodeUIntLE 2 message.volType
    ++ Alpha.encode message.referenceId100
    ++ OtcUnderlyingsGroups.encode message.otcUnderlyingsGroups
    ++ OtcSecurityAltIdGroups.encode message.otcSecurityAltIdGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OtcGroup × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← MdEntrySize.decode bytes
  let (symbol, bytes) ← Alpha.decode 50 bytes
  let (securityGroup12, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 9 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (productOptional, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (restructuringType, bytes) ← Alpha.decode 2 bytes
  let (seniority, bytes) ← Alpha.decode 2 bytes
  let (notionalPercentageOutstanding, bytes) ← decodeUIntLE 4 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePriceDecimalOptional, bytes) ← StrikePriceDecimalOptional.decode bytes
  let (unitOfMeasure, bytes) ← Alpha.decode 5 bytes
  let (unitOfMeasureCurrency, bytes) ← Alpha.decode 3 bytes
  let (unitOfMeasureQtyDecimalOptional, bytes) ← UnitOfMeasureQtyDecimalOptional.decode bytes
  let (mdEntryDate, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (priceType, bytes) ← decodeUIntLE 2 bytes
  let (settlDate, bytes) ← decodeUIntLE 2 bytes
  let (quoteCondition, bytes) ← Alpha.decode 1 bytes
  let (marketSector, bytes) ← Alpha.decode 26 bytes
  let (sectorGroup, bytes) ← Alpha.decode 2 bytes
  let (sectorSubGroup, bytes) ← Alpha.decode 26 bytes
  let (productComplex, bytes) ← Alpha.decode 26 bytes
  let (securitySubType, bytes) ← Alpha.decode 2 bytes
  let (volType, bytes) ← decodeUIntLE 2 bytes
  let (referenceId100, bytes) ← Alpha.decode 100 bytes
  let (otcUnderlyingsGroups, bytes) ← OtcUnderlyingsGroups.decode bytes
  let (otcSecurityAltIdGroups, bytes) ← OtcSecurityAltIdGroups.decode bytes
  pure ({ mdEntryType, rptSeq, mdEntryPx, mdEntrySize, symbol, securityGroup12, securityType, maturityMonthYear, securityExchange, productOptional, maturityDate, couponRate, restructuringType, seniority, notionalPercentageOutstanding, putOrCall, strikePriceDecimalOptional, unitOfMeasure, unitOfMeasureCurrency, unitOfMeasureQtyDecimalOptional, mdEntryDate, openCloseSettlFlag, priceType, settlDate, quoteCondition, marketSector, sectorGroup, sectorSubGroup, productComplex, securitySubType, volType, referenceId100, otcUnderlyingsGroups, otcSecurityAltIdGroups }, bytes)

theorem encode_length_pos (message : OtcGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcGroup) : (encode message).length ≤ 30689 := by
  have bound_otcUnderlyingsGroups := OtcUnderlyingsGroups.encode_length_le message.otcUnderlyingsGroups
  have bound_otcSecurityAltIdGroups := OtcSecurityAltIdGroups.encode_length_le message.otcSecurityAltIdGroups
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, MdEntrySize.encode_length, MaturityMonthYear.encode_length, encodeUInt_length, StrikePriceDecimalOptional.encode_length, UnitOfMeasureQtyDecimalOptional.encode_length]
  omega

@[simp] theorem decode_encode (message : OtcGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [MdEntrySize.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [StrikePriceDecimalOptional.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [UnitOfMeasureQtyDecimalOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OtcUnderlyingsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OtcSecurityAltIdGroups.decode_encode, Option.bind_some]
  rfl

end OtcGroup

/-- Otc Groups -/
structure OtcGroups where
  blockLength : BitVec 16
  otcGroup : Bounded 1 OtcGroup
  deriving DecidableEq, Repr

namespace OtcGroups

def encode (message : OtcGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.otcGroup.val.length)
    ++ encodeMany OtcGroup.encode message.otcGroup.val

def decode (bytes : List UInt8) : Option (OtcGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup8, bytes) ← decodeUInt 1 bytes
  let (otcGroup_, bytes) ← decodeMany OtcGroup.decode numInGroup8.toNat bytes
  if fits_otcGroup : otcGroup_.length < 256 ^ 1 then
    pure ({ blockLength, otcGroup := ⟨otcGroup_, fits_otcGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OtcGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OtcGroups) : (encode message).length ≤ 7825698 := by
  have bound_otcGroup := message.otcGroup.length_lt
  have bound_otcGroup_items := encodeMany_length_le OtcGroup.encode 30689 OtcGroup.encode_length_le message.otcGroup.val
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : OtcGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OtcGroup.encode OtcGroup.decode OtcGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.otcGroup.length_lt, ↓reduceDIte]
  rfl

end OtcGroups

/-- Md Incremental Refresh Ot C 366 -/
structure MdIncrementalRefreshOtC366 where
  transactTime : BitVec 64
  tradeDate : BitVec 16
  matchEventIndicator : BitVec 8
  batchTotalMessagesOptional : BitVec 16
  otcGroups : OtcGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshOtC366

def encode (message : MdIncrementalRefreshOtC366) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.batchTotalMessagesOptional
    ++ OtcGroups.encode message.otcGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshOtC366 × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (batchTotalMessagesOptional, bytes) ← decodeUIntLE 2 bytes
  let (otcGroups, bytes) ← OtcGroups.decode bytes
  pure ({ transactTime, tradeDate, matchEventIndicator, batchTotalMessagesOptional, otcGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshOtC366) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshOtC366) : (encode message).length ≤ 7825711 := by
  have bound_otcGroups := OtcGroups.encode_length_le message.otcGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshOtC366) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OtcGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshOtC366

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | adminHeartbeat (message : AdminHeartbeat) -- 312
  | adminLogin (message : AdminLogin) -- 315
  | adminLogout (message : AdminLogout) -- 316
  | mdIncrementalRefreshErisReferenceDataAndDailyStatistics (message : MdIncrementalRefreshErisReferenceDataAndDailyStatistics) -- 333
  | mdNewsIndices (message : MdNewsIndices) -- 339
  | mdIncrementalRefreshTradeBlocks340 (message : MdIncrementalRefreshTradeBlocks340) -- 340
  | quoteRequest (message : QuoteRequest) -- 345
  | mdInstrumentDefinitionIndices (message : MdInstrumentDefinitionIndices) -- 347
  | mdIncrementalRefreshIndices (message : MdIncrementalRefreshIndices) -- 348
  | mdIncrementalRefreshTradeBlocks349 (message : MdIncrementalRefreshTradeBlocks349) -- 349
  | mdIncrementalRefreshEris351 (message : MdIncrementalRefreshEris351) -- 351
  | mdIncrementalRefreshEris353 (message : MdIncrementalRefreshEris353) -- 353
  | mdIncrementalRefreshOtC356 (message : MdIncrementalRefreshOtC356) -- 356
  | mdInstrumentDefinitionEris (message : MdInstrumentDefinitionEris) -- 363
  | mdIncrementalRefreshTradeBlocks365 (message : MdIncrementalRefreshTradeBlocks365) -- 365
  | mdIncrementalRefreshOtC366 (message : MdIncrementalRefreshOtC366) -- 366
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .adminHeartbeat _ => 312
  | .adminLogin _ => 315
  | .adminLogout _ => 316
  | .mdIncrementalRefreshErisReferenceDataAndDailyStatistics _ => 333
  | .mdNewsIndices _ => 339
  | .mdIncrementalRefreshTradeBlocks340 _ => 340
  | .quoteRequest _ => 345
  | .mdInstrumentDefinitionIndices _ => 347
  | .mdIncrementalRefreshIndices _ => 348
  | .mdIncrementalRefreshTradeBlocks349 _ => 349
  | .mdIncrementalRefreshEris351 _ => 351
  | .mdIncrementalRefreshEris353 _ => 353
  | .mdIncrementalRefreshOtC356 _ => 356
  | .mdInstrumentDefinitionEris _ => 363
  | .mdIncrementalRefreshTradeBlocks365 _ => 365
  | .mdIncrementalRefreshOtC366 _ => 366

def encode : Payload → List UInt8
  | .adminHeartbeat message => AdminHeartbeat.encode message
  | .adminLogin message => AdminLogin.encode message
  | .adminLogout message => AdminLogout.encode message
  | .mdIncrementalRefreshErisReferenceDataAndDailyStatistics message => MdIncrementalRefreshErisReferenceDataAndDailyStatistics.encode message
  | .mdNewsIndices message => MdNewsIndices.encode message
  | .mdIncrementalRefreshTradeBlocks340 message => MdIncrementalRefreshTradeBlocks340.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .mdInstrumentDefinitionIndices message => MdInstrumentDefinitionIndices.encode message
  | .mdIncrementalRefreshIndices message => MdIncrementalRefreshIndices.encode message
  | .mdIncrementalRefreshTradeBlocks349 message => MdIncrementalRefreshTradeBlocks349.encode message
  | .mdIncrementalRefreshEris351 message => MdIncrementalRefreshEris351.encode message
  | .mdIncrementalRefreshEris353 message => MdIncrementalRefreshEris353.encode message
  | .mdIncrementalRefreshOtC356 message => MdIncrementalRefreshOtC356.encode message
  | .mdInstrumentDefinitionEris message => MdInstrumentDefinitionEris.encode message
  | .mdIncrementalRefreshTradeBlocks365 message => MdIncrementalRefreshTradeBlocks365.encode message
  | .mdIncrementalRefreshOtC366 message => MdIncrementalRefreshOtC366.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 312 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
  else if tag = 315 then (AdminLogin.decode bytes).map fun (message, rest) => (.adminLogin message, rest)
  else if tag = 316 then (AdminLogout.decode bytes).map fun (message, rest) => (.adminLogout message, rest)
  else if tag = 333 then (MdIncrementalRefreshErisReferenceDataAndDailyStatistics.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshErisReferenceDataAndDailyStatistics message, rest)
  else if tag = 339 then (MdNewsIndices.decode bytes).map fun (message, rest) => (.mdNewsIndices message, rest)
  else if tag = 340 then (MdIncrementalRefreshTradeBlocks340.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeBlocks340 message, rest)
  else if tag = 345 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 347 then (MdInstrumentDefinitionIndices.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionIndices message, rest)
  else if tag = 348 then (MdIncrementalRefreshIndices.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshIndices message, rest)
  else if tag = 349 then (MdIncrementalRefreshTradeBlocks349.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeBlocks349 message, rest)
  else if tag = 351 then (MdIncrementalRefreshEris351.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshEris351 message, rest)
  else if tag = 353 then (MdIncrementalRefreshEris353.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshEris353 message, rest)
  else if tag = 356 then (MdIncrementalRefreshOtC356.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshOtC356 message, rest)
  else if tag = 363 then (MdInstrumentDefinitionEris.decode bytes).map fun (message, rest) => (.mdInstrumentDefinitionEris message, rest)
  else if tag = 365 then (MdIncrementalRefreshTradeBlocks365.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTradeBlocks365 message, rest)
  else if tag = 366 then (MdIncrementalRefreshOtC366.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshOtC366 message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Tcp Message -/
structure TcpMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace TcpMessage

def encodeBody (message : TcpMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (TcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : TcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : TcpMessage) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2))
    ++ encodeBody message

def decode (bytes : List UInt8) : Option (TcpMessage × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : TcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : TcpMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end TcpMessage

/-- Tcp Packet -/
structure TcpPacket where
  technicalHeader : TechnicalHeader
  tcpMessage : List TcpMessage
  deriving DecidableEq, Repr

namespace TcpPacket

def encode (message : TcpPacket) : List UInt8 :=
  TechnicalHeader.encode message.technicalHeader
    ++ encodeMany TcpMessage.encode message.tcpMessage

def decode (bytes : List UInt8) : Option TcpPacket := do
  let (technicalHeader, bytes) ← TechnicalHeader.decode bytes
  let tcpMessage ← decodeAll TcpMessage.decode bytes.length bytes
  pure { technicalHeader, tcpMessage }

theorem encode_length_pos (message : TcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [TechnicalHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [TechnicalHeader.decode_encode]
  simp only [Option.bind_some]
  rw [decodeAll_encodeMany TcpMessage.encode TcpMessage.decode TcpMessage.decode_encode TcpMessage.encode_length_pos message.tcpMessage _ (encodeMany_length_ge TcpMessage.encode TcpMessage.encode_length_pos message.tcpMessage), Option.bind_some]
  rfl

end TcpPacket

end Omi.CmeGlobexStreamlinedSbeV59Tcp
