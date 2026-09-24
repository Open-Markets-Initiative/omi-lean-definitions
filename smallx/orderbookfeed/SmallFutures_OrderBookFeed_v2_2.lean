import Omi.Wire

/-!
# The Small Exchange Order Book Feed v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Incremental Message Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Trade Conditions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Order Attributes is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Snapshot Message Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SmallxSmallfuturesOrderbookfeedSbeV22

/-- Instrument Trading Status: one byte code -/
def InstrumentTradingStatus.codes : List UInt8 :=
  [0x43, 0x50, 0x4E, 0x4F, 0x55, 0x48]

inductive InstrumentTradingStatus where
  | closed -- Closed
  | preOpen -- Pre Open
  | preOpenNc -- Pre Open Nc
  | open_ -- Open
  | paused -- Paused
  | halted -- Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentTradingStatus

def toByte : InstrumentTradingStatus → UInt8
  | .closed => 0x43
  | .preOpen => 0x50
  | .preOpenNc => 0x4E
  | .open_ => 0x4F
  | .paused => 0x55
  | .halted => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentTradingStatus :=
  if byte = 0x43 then .closed
  else if byte = 0x50 then .preOpen
  else if byte = 0x4E then .preOpenNc
  else if byte = 0x4F then .open_
  else if byte = 0x55 then .paused
  else .halted

def ofByte (byte : UInt8) : InstrumentTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | closed => decide
  | preOpen => decide
  | preOpenNc => decide
  | open_ => decide
  | paused => decide
  | halted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentTradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentTradingStatus

/-- Aggressor Side: one byte code -/
def AggressorSide.codes : List UInt8 :=
  [0x4E, 0x42, 0x53]

inductive AggressorSide where
  | noAggressor -- No Aggressor
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorSide

def toByte : AggressorSide → UInt8
  | .noAggressor => 0x4E
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorSide :=
  if byte = 0x4E then .noAggressor
  else if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : AggressorSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorSide) : ofByte value.toByte = value := by
  cases value with
  | noAggressor => decide
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AggressorSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorSide

/-- Trade Update Action: one byte code -/
def TradeUpdateAction.codes : List UInt8 :=
  [0x4E, 0x44]

inductive TradeUpdateAction where
  | new -- New
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeUpdateAction

def toByte : TradeUpdateAction → UInt8
  | .new => 0x4E
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeUpdateAction :=
  if byte = 0x4E then .new
  else .delete

def ofByte (byte : UInt8) : TradeUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeUpdateAction

/-- Order Update Action: one byte code -/
def OrderUpdateAction.codes : List UInt8 :=
  [0x4E, 0x55, 0x44]

inductive OrderUpdateAction where
  | new -- New
  | update -- Update
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderUpdateAction

def toByte : OrderUpdateAction → UInt8
  | .new => 0x4E
  | .update => 0x55
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderUpdateAction :=
  if byte = 0x4E then .new
  else if byte = 0x55 then .update
  else .delete

def ofByte (byte : UInt8) : OrderUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | update => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderUpdateAction

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
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

/-- Open Price Type: one byte code -/
def OpenPriceType.codes : List UInt8 :=
  [0x49, 0x54, 0x4E]

inductive OpenPriceType where
  | indicative -- Indicative
  | traded -- Traded
  | noPrice -- No Price
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenPriceType

def toByte : OpenPriceType → UInt8
  | .indicative => 0x49
  | .traded => 0x54
  | .noPrice => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenPriceType :=
  if byte = 0x49 then .indicative
  else if byte = 0x54 then .traded
  else .noPrice

def ofByte (byte : UInt8) : OpenPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenPriceType) : ofByte value.toByte = value := by
  cases value with
  | indicative => decide
  | traded => decide
  | noPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenPriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenPriceType

/-- Settlement Price Type: one byte code -/
def SettlementPriceType.codes : List UInt8 :=
  [0x46, 0x50, 0x4E]

inductive SettlementPriceType where
  | final -- Final
  | preliminary -- Preliminary
  | noPrice -- No Price
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementPriceType

def toByte : SettlementPriceType → UInt8
  | .final => 0x46
  | .preliminary => 0x50
  | .noPrice => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementPriceType :=
  if byte = 0x46 then .final
  else if byte = 0x50 then .preliminary
  else .noPrice

def ofByte (byte : UInt8) : SettlementPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementPriceType) : ofByte value.toByte = value := by
  cases value with
  | final => decide
  | preliminary => decide
  | noPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementPriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementPriceType

/-- Instrument Update Action: one byte code -/
def InstrumentUpdateAction.codes : List UInt8 :=
  [0x41, 0x44, 0x4D]

inductive InstrumentUpdateAction where
  | add -- Add
  | delete -- Delete
  | modify -- Modify
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentUpdateAction

def toByte : InstrumentUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .modify => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentUpdateAction :=
  if byte = 0x41 then .add
  else if byte = 0x44 then .delete
  else .modify

def ofByte (byte : UInt8) : InstrumentUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | modify => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentUpdateAction

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x46, 0x4F, 0x4D]

inductive InstrumentType where
  | futures -- Futures
  | option -- Option
  | mleg -- Mleg
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .futures => 0x46
  | .option => 0x4F
  | .mleg => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x46 then .futures
  else if byte = 0x4F then .option
  else .mleg

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | futures => decide
  | option => decide
  | mleg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Put Or Call: one byte code -/
def PutOrCall.codes : List UInt8 :=
  [0x50, 0x43, 0x4E]

inductive PutOrCall where
  | put -- Put
  | call -- Call
  | notOption -- Not Option
  | unlisted (byte : { byte : UInt8 // byte ∉ PutOrCall.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PutOrCall

def toByte : PutOrCall → UInt8
  | .put => 0x50
  | .call => 0x43
  | .notOption => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PutOrCall :=
  if byte = 0x50 then .put
  else if byte = 0x43 then .call
  else .notOption

def ofByte (byte : UInt8) : PutOrCall :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PutOrCall) : ofByte value.toByte = value := by
  cases value with
  | put => decide
  | call => decide
  | notOption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PutOrCall) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PutOrCall × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PutOrCall) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PutOrCall) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PutOrCall

/-- Expiration Style: one byte code -/
def ExpirationStyle.codes : List UInt8 :=
  [0x53, 0x44, 0x57, 0x51]

inductive ExpirationStyle where
  | standard -- Standard
  | daily -- Daily
  | weekly -- Weekly
  | quaterly -- Quaterly
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpirationStyle.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpirationStyle

def toByte : ExpirationStyle → UInt8
  | .standard => 0x53
  | .daily => 0x44
  | .weekly => 0x57
  | .quaterly => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpirationStyle :=
  if byte = 0x53 then .standard
  else if byte = 0x44 then .daily
  else if byte = 0x57 then .weekly
  else .quaterly

def ofByte (byte : UInt8) : ExpirationStyle :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpirationStyle) : ofByte value.toByte = value := by
  cases value with
  | standard => decide
  | daily => decide
  | weekly => decide
  | quaterly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpirationStyle) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpirationStyle × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpirationStyle) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExpirationStyle) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpirationStyle

/-- Exercise Style: one byte code -/
def ExerciseStyle.codes : List UInt8 :=
  [0x45, 0x41, 0x4E]

inductive ExerciseStyle where
  | european -- European
  | american -- American
  | notOption -- Not Option
  | unlisted (byte : { byte : UInt8 // byte ∉ ExerciseStyle.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExerciseStyle

def toByte : ExerciseStyle → UInt8
  | .european => 0x45
  | .american => 0x41
  | .notOption => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExerciseStyle :=
  if byte = 0x45 then .european
  else if byte = 0x41 then .american
  else .notOption

def ofByte (byte : UInt8) : ExerciseStyle :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExerciseStyle) : ofByte value.toByte = value := by
  cases value with
  | european => decide
  | american => decide
  | notOption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExerciseStyle) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExerciseStyle × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExerciseStyle) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExerciseStyle) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExerciseStyle

/-- Delivery: one byte code -/
def Delivery.codes : List UInt8 :=
  [0x43, 0x50]

inductive Delivery where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ Delivery.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Delivery

def toByte : Delivery → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Delivery :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : Delivery :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Delivery) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Delivery) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Delivery × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Delivery) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Delivery) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Delivery

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive LegSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .buy
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

/-- Packet Header: 10 bytes -/
structure PacketHeader where
  channelId : BitVec 8
  incarnation : BitVec 16
  source : BitVec 8
  packetFlags : BitVec 8
  messageSequence : BitVec 32
  messageCount : BitVec 8
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  encodeUInt 1 message.channelId
    ++ (encodeUIntLE 2 message.incarnation
    ++ (encodeUInt 1 message.source
    ++ (encodeUIntLE 1 message.packetFlags
    ++ (encodeUIntLE 4 message.messageSequence
    ++ (encodeUInt 1 message.messageCount)))))

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (channelId, bytes) ← decodeUInt 1 bytes
  let (incarnation, bytes) ← decodeUIntLE 2 bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (packetFlags, bytes) ← decodeUIntLE 1 bytes
  let (messageSequence, bytes) ← decodeUIntLE 4 bytes
  let (messageCount, bytes) ← decodeUInt 1 bytes
  pure ({ channelId, incarnation, source, packetFlags, messageSequence, messageCount }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PacketHeader

/-- Instrument Trading Status Incremental Message: 25 bytes -/
structure InstrumentTradingStatusIncrementalMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  deriving DecidableEq, Repr

namespace InstrumentTradingStatusIncrementalMessage

def encode (message : InstrumentTradingStatusIncrementalMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions)))))

def decode (bytes : List UInt8) : Option (InstrumentTradingStatusIncrementalMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions }, bytes)

@[simp] theorem encode_length (message : InstrumentTradingStatusIncrementalMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentTradingStatus.encode_length]

theorem encode_length_pos (message : InstrumentTradingStatusIncrementalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentTradingStatusIncrementalMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentTradingStatusIncrementalMessage

/-- Incremental Trade Group: 43 bytes -/
structure IncrementalTradeGroup where
  tradeId : BitVec 64
  price : BitVec 64
  size : BitVec 64
  aggressorSide : AggressorSide
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  tradeConditions : BitVec 16
  deriving DecidableEq, Repr

namespace IncrementalTradeGroup

def encode (message : IncrementalTradeGroup) : List UInt8 :=
  encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.size
    ++ (AggressorSide.encode message.aggressorSide
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 2 message.tradeConditions))))))

def decode (bytes : List UInt8) : Option (IncrementalTradeGroup × List UInt8) := do
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← AggressorSide.decode bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeConditions, bytes) ← decodeUIntLE 2 bytes
  pure ({ tradeId, price, size, aggressorSide, buyOrderId, sellOrderId, tradeConditions }, bytes)

@[simp] theorem encode_length (message : IncrementalTradeGroup) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AggressorSide.encode_length]

theorem encode_length_pos (message : IncrementalTradeGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalTradeGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IncrementalTradeGroup

/-- Incremental Trade Groups -/
structure IncrementalTradeGroups where
  blockLength : BitVec 16
  incrementalTradeGroup : Bounded 1 IncrementalTradeGroup
  deriving DecidableEq, Repr

namespace IncrementalTradeGroups

def encode (message : IncrementalTradeGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalTradeGroup.val.length)
    ++ (encodeMany IncrementalTradeGroup.encode message.incrementalTradeGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalTradeGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalTradeGroup_, bytes) ← decodeMany IncrementalTradeGroup.decode numInGroup.toNat bytes
  if fits_incrementalTradeGroup : incrementalTradeGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalTradeGroup := ⟨incrementalTradeGroup_, fits_incrementalTradeGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalTradeGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalTradeGroups) : (encode message).length ≤ 10968 := by
  have bound_incrementalTradeGroup := message.incrementalTradeGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalTradeGroup.encode 43 IncrementalTradeGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalTradeGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalTradeGroup.encode IncrementalTradeGroup.decode IncrementalTradeGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalTradeGroup.length_lt]
  rfl

end IncrementalTradeGroups

/-- Trades Incremental Message -/
structure TradesIncrementalMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  lastTradePrice : BitVec 64
  lastTradeSize : BitVec 64
  lastTradeTimeTimestampOptional : BitVec 64
  totalVolumeQuantity : BitVec 64
  incrementalTradeGroups : IncrementalTradeGroups
  deriving DecidableEq, Repr

namespace TradesIncrementalMessage

def encode (message : TradesIncrementalMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeSize
    ++ (encodeUIntLE 8 message.lastTradeTimeTimestampOptional
    ++ (encodeUIntLE 8 message.totalVolumeQuantity
    ++ (IncrementalTradeGroups.encode message.incrementalTradeGroups))))))))))

def decode (bytes : List UInt8) : Option (TradesIncrementalMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeSize, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTimeTimestampOptional, bytes) ← decodeUIntLE 8 bytes
  let (totalVolumeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (incrementalTradeGroups, bytes) ← IncrementalTradeGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, lastTradePrice, lastTradeSize, lastTradeTimeTimestampOptional, totalVolumeQuantity, incrementalTradeGroups }, bytes)

theorem encode_length_pos (message : TradesIncrementalMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradesIncrementalMessage) : (encode message).length ≤ 11025 := by
  have bound_incrementalTradeGroups := IncrementalTradeGroups.encode_length_le message.incrementalTradeGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : TradesIncrementalMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [IncrementalTradeGroups.decode_encode, some_bind]
  rfl

end TradesIncrementalMessage

/-- Trade Correct Group: 52 bytes -/
structure TradeCorrectGroup where
  tradeUpdateAction : TradeUpdateAction
  tradeId : BitVec 64
  time : BitVec 64
  price : BitVec 64
  size : BitVec 64
  aggressorSide : AggressorSide
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  tradeConditions : BitVec 16
  deriving DecidableEq, Repr

namespace TradeCorrectGroup

def encode (message : TradeCorrectGroup) : List UInt8 :=
  TradeUpdateAction.encode message.tradeUpdateAction
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.time
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.size
    ++ (AggressorSide.encode message.aggressorSide
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 2 message.tradeConditions))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectGroup × List UInt8) := do
  let (tradeUpdateAction, bytes) ← TradeUpdateAction.decode bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (time, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← AggressorSide.decode bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeConditions, bytes) ← decodeUIntLE 2 bytes
  pure ({ tradeUpdateAction, tradeId, time, price, size, aggressorSide, buyOrderId, sellOrderId, tradeConditions }, bytes)

@[simp] theorem encode_length (message : TradeCorrectGroup) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, TradeUpdateAction.encode_length, encodeUIntLE_length, AggressorSide.encode_length]

theorem encode_length_pos (message : TradeCorrectGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradeUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCorrectGroup

/-- Trade Correct Groups -/
structure TradeCorrectGroups where
  blockLength : BitVec 16
  tradeCorrectGroup : Bounded 1 TradeCorrectGroup
  deriving DecidableEq, Repr

namespace TradeCorrectGroups

def encode (message : TradeCorrectGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeCorrectGroup.val.length)
    ++ (encodeMany TradeCorrectGroup.encode message.tradeCorrectGroup.val))

def decode (bytes : List UInt8) : Option (TradeCorrectGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeCorrectGroup_, bytes) ← decodeMany TradeCorrectGroup.decode numInGroup.toNat bytes
  if fits_tradeCorrectGroup : tradeCorrectGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeCorrectGroup := ⟨tradeCorrectGroup_, fits_tradeCorrectGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeCorrectGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeCorrectGroups) : (encode message).length ≤ 13263 := by
  have bound_tradeCorrectGroup := message.tradeCorrectGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeCorrectGroup.encode 52 TradeCorrectGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeCorrectGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TradeCorrectGroup.encode TradeCorrectGroup.decode TradeCorrectGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeCorrectGroup.length_lt]
  rfl

end TradeCorrectGroups

/-- Trade Correct Message -/
structure TradeCorrectMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  lastTradePrice : BitVec 64
  lastTradeSize : BitVec 64
  lastTradeTimeTimestampOptional : BitVec 64
  totalVolumeQuantity : BitVec 64
  tradeCorrectGroups : TradeCorrectGroups
  deriving DecidableEq, Repr

namespace TradeCorrectMessage

def encode (message : TradeCorrectMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeSize
    ++ (encodeUIntLE 8 message.lastTradeTimeTimestampOptional
    ++ (encodeUIntLE 8 message.totalVolumeQuantity
    ++ (TradeCorrectGroups.encode message.tradeCorrectGroups))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeSize, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTimeTimestampOptional, bytes) ← decodeUIntLE 8 bytes
  let (totalVolumeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeCorrectGroups, bytes) ← TradeCorrectGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, lastTradePrice, lastTradeSize, lastTradeTimeTimestampOptional, totalVolumeQuantity, tradeCorrectGroups }, bytes)

theorem encode_length_pos (message : TradeCorrectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeCorrectMessage) : (encode message).length ≤ 13320 := by
  have bound_tradeCorrectGroups := TradeCorrectGroups.encode_length_le message.tradeCorrectGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeCorrectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [TradeCorrectGroups.decode_encode, some_bind]
  rfl

end TradeCorrectMessage

/-- Trade Bust Group: 51 bytes -/
structure TradeBustGroup where
  tradeId : BitVec 64
  time : BitVec 64
  price : BitVec 64
  size : BitVec 64
  aggressorSide : AggressorSide
  buyOrderId : BitVec 64
  sellOrderId : BitVec 64
  tradeConditions : BitVec 16
  deriving DecidableEq, Repr

namespace TradeBustGroup

def encode (message : TradeBustGroup) : List UInt8 :=
  encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.time
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.size
    ++ (AggressorSide.encode message.aggressorSide
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 2 message.tradeConditions)))))))

def decode (bytes : List UInt8) : Option (TradeBustGroup × List UInt8) := do
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (time, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (aggressorSide, bytes) ← AggressorSide.decode bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeConditions, bytes) ← decodeUIntLE 2 bytes
  pure ({ tradeId, time, price, size, aggressorSide, buyOrderId, sellOrderId, tradeConditions }, bytes)

@[simp] theorem encode_length (message : TradeBustGroup) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, AggressorSide.encode_length]

theorem encode_length_pos (message : TradeBustGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, AggressorSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBustGroup

/-- Trade Bust Groups -/
structure TradeBustGroups where
  blockLength : BitVec 16
  tradeBustGroup : Bounded 1 TradeBustGroup
  deriving DecidableEq, Repr

namespace TradeBustGroups

def encode (message : TradeBustGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeBustGroup.val.length)
    ++ (encodeMany TradeBustGroup.encode message.tradeBustGroup.val))

def decode (bytes : List UInt8) : Option (TradeBustGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeBustGroup_, bytes) ← decodeMany TradeBustGroup.decode numInGroup.toNat bytes
  if fits_tradeBustGroup : tradeBustGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeBustGroup := ⟨tradeBustGroup_, fits_tradeBustGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeBustGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBustGroups) : (encode message).length ≤ 13008 := by
  have bound_tradeBustGroup := message.tradeBustGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeBustGroup.encode 51 TradeBustGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBustGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TradeBustGroup.encode TradeBustGroup.decode TradeBustGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeBustGroup.length_lt]
  rfl

end TradeBustGroups

/-- Trade Bust Message -/
structure TradeBustMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  lastTradePrice : BitVec 64
  lastTradeSize : BitVec 64
  lastTradeTimeTimestampOptional : BitVec 64
  totalVolumeQuantity : BitVec 64
  tradeBustGroups : TradeBustGroups
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeSize
    ++ (encodeUIntLE 8 message.lastTradeTimeTimestampOptional
    ++ (encodeUIntLE 8 message.totalVolumeQuantity
    ++ (TradeBustGroups.encode message.tradeBustGroups))))))))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeSize, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTimeTimestampOptional, bytes) ← decodeUIntLE 8 bytes
  let (totalVolumeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeBustGroups, bytes) ← TradeBustGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, lastTradePrice, lastTradeSize, lastTradeTimeTimestampOptional, totalVolumeQuantity, tradeBustGroups }, bytes)

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeBustMessage) : (encode message).length ≤ 13065 := by
  have bound_tradeBustGroups := TradeBustGroups.encode_length_le message.tradeBustGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [TradeBustGroups.decode_encode, some_bind]
  rfl

end TradeBustMessage

/-- Incremetal Orders Group: 44 bytes -/
structure IncremetalOrdersGroup where
  orderUpdateAction : OrderUpdateAction
  orderId : BitVec 64
  tradeIdOptional : BitVec 64
  side : Side
  priceOptional : BitVec 64
  size : BitVec 64
  orderPriorityOptional : BitVec 64
  orderAttributes : BitVec 16
  deriving DecidableEq, Repr

namespace IncremetalOrdersGroup

def encode (message : IncremetalOrdersGroup) : List UInt8 :=
  OrderUpdateAction.encode message.orderUpdateAction
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.tradeIdOptional
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.priceOptional
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.orderPriorityOptional
    ++ (encodeUIntLE 2 message.orderAttributes)))))))

def decode (bytes : List UInt8) : Option (IncremetalOrdersGroup × List UInt8) := do
  let (orderUpdateAction, bytes) ← OrderUpdateAction.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (orderPriorityOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderAttributes, bytes) ← decodeUIntLE 2 bytes
  pure ({ orderUpdateAction, orderId, tradeIdOptional, side, priceOptional, size, orderPriorityOptional, orderAttributes }, bytes)

@[simp] theorem encode_length (message : IncremetalOrdersGroup) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, OrderUpdateAction.encode_length, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : IncremetalOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncremetalOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OrderUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IncremetalOrdersGroup

/-- Incremetal Orders Groups -/
structure IncremetalOrdersGroups where
  blockLength : BitVec 16
  incremetalOrdersGroup : Bounded 1 IncremetalOrdersGroup
  deriving DecidableEq, Repr

namespace IncremetalOrdersGroups

def encode (message : IncremetalOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incremetalOrdersGroup.val.length)
    ++ (encodeMany IncremetalOrdersGroup.encode message.incremetalOrdersGroup.val))

def decode (bytes : List UInt8) : Option (IncremetalOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incremetalOrdersGroup_, bytes) ← decodeMany IncremetalOrdersGroup.decode numInGroup.toNat bytes
  if fits_incremetalOrdersGroup : incremetalOrdersGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incremetalOrdersGroup := ⟨incremetalOrdersGroup_, fits_incremetalOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncremetalOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncremetalOrdersGroups) : (encode message).length ≤ 11223 := by
  have bound_incremetalOrdersGroup := message.incremetalOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncremetalOrdersGroup.encode 44 IncremetalOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncremetalOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncremetalOrdersGroup.encode IncremetalOrdersGroup.decode IncremetalOrdersGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incremetalOrdersGroup.length_lt]
  rfl

end IncremetalOrdersGroups

/-- Order Book Incremental Message -/
structure OrderBookIncrementalMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  incremetalOrdersGroups : IncremetalOrdersGroups
  deriving DecidableEq, Repr

namespace OrderBookIncrementalMessage

def encode (message : OrderBookIncrementalMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (IncremetalOrdersGroups.encode message.incremetalOrdersGroups))))))

def decode (bytes : List UInt8) : Option (OrderBookIncrementalMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (incremetalOrdersGroups, bytes) ← IncremetalOrdersGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, incremetalOrdersGroups }, bytes)

theorem encode_length_pos (message : OrderBookIncrementalMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookIncrementalMessage) : (encode message).length ≤ 11248 := by
  have bound_incremetalOrdersGroups := IncremetalOrdersGroups.encode_length_le message.incremetalOrdersGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderBookIncrementalMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [IncremetalOrdersGroups.decode_encode, some_bind]
  rfl

end OrderBookIncrementalMessage

/-- Market Summary Incremental Message: 75 bytes -/
structure MarketSummaryIncrementalMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  openPrice : BitVec 64
  openPriceType : OpenPriceType
  highPrice : BitVec 64
  lowPrice : BitVec 64
  closePrice : BitVec 64
  openInterest : BitVec 64
  settlementPrice : BitVec 64
  settlementPriceType : SettlementPriceType
  deriving DecidableEq, Repr

namespace MarketSummaryIncrementalMessage

def encode (message : MarketSummaryIncrementalMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (encodeUIntLE 8 message.openPrice
    ++ (OpenPriceType.encode message.openPriceType
    ++ (encodeUIntLE 8 message.highPrice
    ++ (encodeUIntLE 8 message.lowPrice
    ++ (encodeUIntLE 8 message.closePrice
    ++ (encodeUIntLE 8 message.openInterest
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (SettlementPriceType.encode message.settlementPriceType)))))))))))))

def decode (bytes : List UInt8) : Option (MarketSummaryIncrementalMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (openPrice, bytes) ← decodeUIntLE 8 bytes
  let (openPriceType, bytes) ← OpenPriceType.decode bytes
  let (highPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowPrice, bytes) ← decodeUIntLE 8 bytes
  let (closePrice, bytes) ← decodeUIntLE 8 bytes
  let (openInterest, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPriceType, bytes) ← SettlementPriceType.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, openPrice, openPriceType, highPrice, lowPrice, closePrice, openInterest, settlementPrice, settlementPriceType }, bytes)

@[simp] theorem encode_length (message : MarketSummaryIncrementalMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentTradingStatus.encode_length, OpenPriceType.encode_length, SettlementPriceType.encode_length]

theorem encode_length_pos (message : MarketSummaryIncrementalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSummaryIncrementalMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceType.decode_encode, some_bind]
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
  rw [SettlementPriceType.decode_encode, some_bind]
  rfl

end MarketSummaryIncrementalMessage

/-- Snaphot Orders Group: 43 bytes -/
structure SnaphotOrdersGroup where
  orderId : BitVec 64
  side : Side
  price : BitVec 64
  size : BitVec 64
  orderPriority : BitVec 64
  orderAttributes : BitVec 16
  time : BitVec 64
  deriving DecidableEq, Repr

namespace SnaphotOrdersGroup

def encode (message : SnaphotOrdersGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.size
    ++ (encodeUIntLE 8 message.orderPriority
    ++ (encodeUIntLE 2 message.orderAttributes
    ++ (encodeUIntLE 8 message.time))))))

def decode (bytes : List UInt8) : Option (SnaphotOrdersGroup × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 8 bytes
  let (orderPriority, bytes) ← decodeUIntLE 8 bytes
  let (orderAttributes, bytes) ← decodeUIntLE 2 bytes
  let (time, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderId, side, price, size, orderPriority, orderAttributes, time }, bytes)

@[simp] theorem encode_length (message : SnaphotOrdersGroup) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

theorem encode_length_pos (message : SnaphotOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnaphotOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end SnaphotOrdersGroup

/-- Snaphot Orders Groups -/
structure SnaphotOrdersGroups where
  blockLength : BitVec 16
  snaphotOrdersGroup : Bounded 1 SnaphotOrdersGroup
  deriving DecidableEq, Repr

namespace SnaphotOrdersGroups

def encode (message : SnaphotOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.snaphotOrdersGroup.val.length)
    ++ (encodeMany SnaphotOrdersGroup.encode message.snaphotOrdersGroup.val))

def decode (bytes : List UInt8) : Option (SnaphotOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snaphotOrdersGroup_, bytes) ← decodeMany SnaphotOrdersGroup.decode numInGroup.toNat bytes
  if fits_snaphotOrdersGroup : snaphotOrdersGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snaphotOrdersGroup := ⟨snaphotOrdersGroup_, fits_snaphotOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnaphotOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnaphotOrdersGroups) : (encode message).length ≤ 10968 := by
  have bound_snaphotOrdersGroup := message.snaphotOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnaphotOrdersGroup.encode 43 SnaphotOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnaphotOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SnaphotOrdersGroup.encode SnaphotOrdersGroup.decode SnaphotOrdersGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.snaphotOrdersGroup.length_lt]
  rfl

end SnaphotOrdersGroups

/-- Order Book Snapshot Message -/
structure OrderBookSnapshotMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  snapshotMessageInstructions : BitVec 16
  snapshotInstrumentsCount : BitVec 32
  lastIncrementalMessageSeq : BitVec 64
  snaphotOrdersGroups : SnaphotOrdersGroups
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessage

def encode (message : OrderBookSnapshotMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.snapshotMessageInstructions
    ++ (encodeUIntLE 4 message.snapshotInstrumentsCount
    ++ (encodeUIntLE 8 message.lastIncrementalMessageSeq
    ++ (SnaphotOrdersGroups.encode message.snaphotOrdersGroups))))))))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (snapshotMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (snapshotInstrumentsCount, bytes) ← decodeUIntLE 4 bytes
  let (lastIncrementalMessageSeq, bytes) ← decodeUIntLE 8 bytes
  let (snaphotOrdersGroups, bytes) ← SnaphotOrdersGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, snapshotMessageInstructions, snapshotInstrumentsCount, lastIncrementalMessageSeq, snaphotOrdersGroups }, bytes)

theorem encode_length_pos (message : OrderBookSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookSnapshotMessage) : (encode message).length ≤ 11005 := by
  have bound_snaphotOrdersGroups := SnaphotOrdersGroups.encode_length_le message.snaphotOrdersGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderBookSnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SnaphotOrdersGroups.decode_encode, some_bind]
  rfl

end OrderBookSnapshotMessage

/-- Market Summary Snapshot Message: 119 bytes -/
structure MarketSummarySnapshotMessage where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  snapshotMessageInstructions : BitVec 16
  snapshotInstrumentsCount : BitVec 32
  lastIncrementalMessageSeq : BitVec 64
  lastTradePrice : BitVec 64
  lastTradeSize : BitVec 64
  lastTradeTimeTimestamp : BitVec 64
  totalVolumeQuantityOptional : BitVec 64
  openPrice : BitVec 64
  openPriceType : OpenPriceType
  highPrice : BitVec 64
  lowPrice : BitVec 64
  closePrice : BitVec 64
  openInterest : BitVec 64
  settlementPrice : BitVec 64
  settlementPriceType : SettlementPriceType
  deriving DecidableEq, Repr

namespace MarketSummarySnapshotMessage

def encode (message : MarketSummarySnapshotMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.snapshotMessageInstructions
    ++ (encodeUIntLE 4 message.snapshotInstrumentsCount
    ++ (encodeUIntLE 8 message.lastIncrementalMessageSeq
    ++ (encodeUIntLE 8 message.lastTradePrice
    ++ (encodeUIntLE 8 message.lastTradeSize
    ++ (encodeUIntLE 8 message.lastTradeTimeTimestamp
    ++ (encodeUIntLE 8 message.totalVolumeQuantityOptional
    ++ (encodeUIntLE 8 message.openPrice
    ++ (OpenPriceType.encode message.openPriceType
    ++ (encodeUIntLE 8 message.highPrice
    ++ (encodeUIntLE 8 message.lowPrice
    ++ (encodeUIntLE 8 message.closePrice
    ++ (encodeUIntLE 8 message.openInterest
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (SettlementPriceType.encode message.settlementPriceType)))))))))))))))))))

def decode (bytes : List UInt8) : Option (MarketSummarySnapshotMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (snapshotMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (snapshotInstrumentsCount, bytes) ← decodeUIntLE 4 bytes
  let (lastIncrementalMessageSeq, bytes) ← decodeUIntLE 8 bytes
  let (lastTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeSize, bytes) ← decodeUIntLE 8 bytes
  let (lastTradeTimeTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (totalVolumeQuantityOptional, bytes) ← decodeUIntLE 8 bytes
  let (openPrice, bytes) ← decodeUIntLE 8 bytes
  let (openPriceType, bytes) ← OpenPriceType.decode bytes
  let (highPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowPrice, bytes) ← decodeUIntLE 8 bytes
  let (closePrice, bytes) ← decodeUIntLE 8 bytes
  let (openInterest, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPriceType, bytes) ← SettlementPriceType.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, snapshotMessageInstructions, snapshotInstrumentsCount, lastIncrementalMessageSeq, lastTradePrice, lastTradeSize, lastTradeTimeTimestamp, totalVolumeQuantityOptional, openPrice, openPriceType, highPrice, lowPrice, closePrice, openInterest, settlementPrice, settlementPriceType }, bytes)

@[simp] theorem encode_length (message : MarketSummarySnapshotMessage) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentTradingStatus.encode_length, OpenPriceType.encode_length, SettlementPriceType.encode_length]

theorem encode_length_pos (message : MarketSummarySnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSummarySnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenPriceType.decode_encode, some_bind]
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
  rw [SettlementPriceType.decode_encode, some_bind]
  rfl

end MarketSummarySnapshotMessage

/-- Index Value Snapshot Message: 80 bytes -/
structure IndexValueSnapshotMessage where
  instrumentId : BitVec 32
  transactTime : BitVec 64
  snapshotMessageInstructions : BitVec 16
  indexCount : BitVec 32
  indexSymbol : Alpha 20
  value : BitVec 64
  sessionDate : BitVec 16
  openPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  closePrice : BitVec 64
  deriving DecidableEq, Repr

namespace IndexValueSnapshotMessage

def encode (message : IndexValueSnapshotMessage) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.snapshotMessageInstructions
    ++ (encodeUIntLE 4 message.indexCount
    ++ (Alpha.encode message.indexSymbol
    ++ (encodeUIntLE 8 message.value
    ++ (encodeUIntLE 2 message.sessionDate
    ++ (encodeUIntLE 8 message.openPrice
    ++ (encodeUIntLE 8 message.highPrice
    ++ (encodeUIntLE 8 message.lowPrice
    ++ (encodeUIntLE 8 message.closePrice))))))))))

def decode (bytes : List UInt8) : Option (IndexValueSnapshotMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (snapshotMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (indexCount, bytes) ← decodeUIntLE 4 bytes
  let (indexSymbol, bytes) ← Alpha.decode 20 bytes
  let (value, bytes) ← decodeUIntLE 8 bytes
  let (sessionDate, bytes) ← decodeUIntLE 2 bytes
  let (openPrice, bytes) ← decodeUIntLE 8 bytes
  let (highPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowPrice, bytes) ← decodeUIntLE 8 bytes
  let (closePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, transactTime, snapshotMessageInstructions, indexCount, indexSymbol, value, sessionDate, openPrice, highPrice, lowPrice, closePrice }, bytes)

@[simp] theorem encode_length (message : IndexValueSnapshotMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexValueSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexValueSnapshotMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexValueSnapshotMessage

/-- Single Instrument Definition Incremental V 2 Message: 262 bytes -/
structure SingleInstrumentDefinitionIncrementalV2Message where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  instrumentUpdateAction : InstrumentUpdateAction
  symbol : Alpha 25
  product : Alpha 8
  description : Alpha 120
  instrumentType : InstrumentType
  maturityDate : BitVec 16
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  expirationDate : BitVec 16
  cfiCode : Alpha 6
  currency : Alpha 3
  priceIncrement : BitVec 64
  priceMultiplier : BitVec 64
  underlyingSymbol : Alpha 25
  underlyingInstrumentId : BitVec 32
  putOrCall : PutOrCall
  strikePrice : BitVec 64
  sharesPerContract : BitVec 64
  expirationStyle : ExpirationStyle
  exerciseStyle : ExerciseStyle
  delivery : Delivery
  deriving DecidableEq, Repr

namespace SingleInstrumentDefinitionIncrementalV2Message

def encode (message : SingleInstrumentDefinitionIncrementalV2Message) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (InstrumentUpdateAction.encode message.instrumentUpdateAction
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.product
    ++ (Alpha.encode message.description
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.expirationDate
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 8 message.priceIncrement
    ++ (encodeUIntLE 8 message.priceMultiplier
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.underlyingInstrumentId
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.sharesPerContract
    ++ (ExpirationStyle.encode message.expirationStyle
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (Delivery.encode message.delivery))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SingleInstrumentDefinitionIncrementalV2Message × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (instrumentUpdateAction, bytes) ← InstrumentUpdateAction.decode bytes
  let (symbol, bytes) ← Alpha.decode 25 bytes
  let (product, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 120 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (expirationDate, bytes) ← decodeUIntLE 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (priceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 25 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (sharesPerContract, bytes) ← decodeUIntLE 8 bytes
  let (expirationStyle, bytes) ← ExpirationStyle.decode bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (delivery, bytes) ← Delivery.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, instrumentUpdateAction, symbol, product, description, instrumentType, maturityDate, firstTradingSessionDate, lastTradingSessionDate, expirationDate, cfiCode, currency, priceIncrement, priceMultiplier, underlyingSymbol, underlyingInstrumentId, putOrCall, strikePrice, sharesPerContract, expirationStyle, exerciseStyle, delivery }, bytes)

@[simp] theorem encode_length (message : SingleInstrumentDefinitionIncrementalV2Message) : (encode message).length = 262 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentTradingStatus.encode_length, InstrumentUpdateAction.encode_length, Alpha.encode_length, InstrumentType.encode_length, PutOrCall.encode_length, ExpirationStyle.encode_length, ExerciseStyle.encode_length, Delivery.encode_length]

theorem encode_length_pos (message : SingleInstrumentDefinitionIncrementalV2Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SingleInstrumentDefinitionIncrementalV2Message) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [Delivery.decode_encode, some_bind]
  rfl

end SingleInstrumentDefinitionIncrementalV2Message

/-- Legs Group: 46 bytes -/
structure LegsGroup where
  legInstrumentId : BitVec 32
  legSymbol : Alpha 25
  legProduct : Alpha 8
  legRatioQuantity : BitVec 64
  legSide : LegSide
  deriving DecidableEq, Repr

namespace LegsGroup

def encode (message : LegsGroup) : List UInt8 :=
  encodeUIntLE 4 message.legInstrumentId
    ++ (Alpha.encode message.legSymbol
    ++ (Alpha.encode message.legProduct
    ++ (encodeUIntLE 8 message.legRatioQuantity
    ++ (LegSide.encode message.legSide))))

def decode (bytes : List UInt8) : Option (LegsGroup × List UInt8) := do
  let (legInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legSymbol, bytes) ← Alpha.decode 25 bytes
  let (legProduct, bytes) ← Alpha.decode 8 bytes
  let (legRatioQuantity, bytes) ← decodeUIntLE 8 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  pure ({ legInstrumentId, legSymbol, legProduct, legRatioQuantity, legSide }, bytes)

@[simp] theorem encode_length (message : LegsGroup) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LegSide.encode_length]

theorem encode_length_pos (message : LegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [LegSide.decode_encode, some_bind]
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
theorem encode_length_le (message : LegsGroups) : (encode message).length ≤ 11733 := by
  have bound_legsGroup := message.legsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegsGroup.encode 46 LegsGroup.encode_length]
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

/-- Multileg Definition Incremental V 2 Message -/
structure MultilegDefinitionIncrementalV2Message where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  incrementalMessageInstructions : BitVec 16
  instrumentUpdateAction : InstrumentUpdateAction
  spreadSymbol : Alpha 120
  description : Alpha 120
  instrumentType : InstrumentType
  maturityDate : BitVec 16
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  expirationDate : BitVec 16
  cfiCode : Alpha 6
  currency : Alpha 3
  priceIncrement : BitVec 64
  priceMultiplier : BitVec 64
  strategyType : BitVec 8
  legsGroups : LegsGroups
  deriving DecidableEq, Repr

namespace MultilegDefinitionIncrementalV2Message

def encode (message : MultilegDefinitionIncrementalV2Message) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.incrementalMessageInstructions
    ++ (InstrumentUpdateAction.encode message.instrumentUpdateAction
    ++ (Alpha.encode message.spreadSymbol
    ++ (Alpha.encode message.description
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.expirationDate
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 8 message.priceIncrement
    ++ (encodeUIntLE 8 message.priceMultiplier
    ++ (encodeUInt 1 message.strategyType
    ++ (LegsGroups.encode message.legsGroups)))))))))))))))))))

def decode (bytes : List UInt8) : Option (MultilegDefinitionIncrementalV2Message × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (incrementalMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (instrumentUpdateAction, bytes) ← InstrumentUpdateAction.decode bytes
  let (spreadSymbol, bytes) ← Alpha.decode 120 bytes
  let (description, bytes) ← Alpha.decode 120 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (expirationDate, bytes) ← decodeUIntLE 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (priceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (strategyType, bytes) ← decodeUInt 1 bytes
  let (legsGroups, bytes) ← LegsGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, incrementalMessageInstructions, instrumentUpdateAction, spreadSymbol, description, instrumentType, maturityDate, firstTradingSessionDate, lastTradingSessionDate, expirationDate, cfiCode, currency, priceIncrement, priceMultiplier, strategyType, legsGroups }, bytes)

theorem encode_length_pos (message : MultilegDefinitionIncrementalV2Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultilegDefinitionIncrementalV2Message) : (encode message).length ≤ 12034 := by
  have bound_legsGroups := LegsGroups.encode_length_le message.legsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length, InstrumentUpdateAction.encode_length, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MultilegDefinitionIncrementalV2Message) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LegsGroups.decode_encode, some_bind]
  rfl

end MultilegDefinitionIncrementalV2Message

/-- Single Instrument Definition Snapshot V 2 Message: 273 bytes -/
structure SingleInstrumentDefinitionSnapshotV2Message where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  snapshotMessageInstructions : BitVec 16
  snapshotInstrumentsCount : BitVec 32
  lastIncrementalMessageSeq : BitVec 64
  symbol : Alpha 25
  product : Alpha 8
  description : Alpha 120
  instrumentType : InstrumentType
  maturityDate : BitVec 16
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  expirationDate : BitVec 16
  cfiCode : Alpha 6
  currency : Alpha 3
  priceIncrement : BitVec 64
  priceMultiplier : BitVec 64
  underlyingSymbol : Alpha 25
  underlyingInstrumentId : BitVec 32
  putOrCall : PutOrCall
  strikePrice : BitVec 64
  sharesPerContract : BitVec 64
  expirationStyle : ExpirationStyle
  exerciseStyle : ExerciseStyle
  delivery : Delivery
  deriving DecidableEq, Repr

namespace SingleInstrumentDefinitionSnapshotV2Message

def encode (message : SingleInstrumentDefinitionSnapshotV2Message) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.snapshotMessageInstructions
    ++ (encodeUIntLE 4 message.snapshotInstrumentsCount
    ++ (encodeUIntLE 8 message.lastIncrementalMessageSeq
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.product
    ++ (Alpha.encode message.description
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.expirationDate
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 8 message.priceIncrement
    ++ (encodeUIntLE 8 message.priceMultiplier
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.underlyingInstrumentId
    ++ (PutOrCall.encode message.putOrCall
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.sharesPerContract
    ++ (ExpirationStyle.encode message.expirationStyle
    ++ (ExerciseStyle.encode message.exerciseStyle
    ++ (Delivery.encode message.delivery)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SingleInstrumentDefinitionSnapshotV2Message × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (snapshotMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (snapshotInstrumentsCount, bytes) ← decodeUIntLE 4 bytes
  let (lastIncrementalMessageSeq, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 25 bytes
  let (product, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 120 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (expirationDate, bytes) ← decodeUIntLE 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (priceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 25 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (putOrCall, bytes) ← PutOrCall.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (sharesPerContract, bytes) ← decodeUIntLE 8 bytes
  let (expirationStyle, bytes) ← ExpirationStyle.decode bytes
  let (exerciseStyle, bytes) ← ExerciseStyle.decode bytes
  let (delivery, bytes) ← Delivery.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, snapshotMessageInstructions, snapshotInstrumentsCount, lastIncrementalMessageSeq, symbol, product, description, instrumentType, maturityDate, firstTradingSessionDate, lastTradingSessionDate, expirationDate, cfiCode, currency, priceIncrement, priceMultiplier, underlyingSymbol, underlyingInstrumentId, putOrCall, strikePrice, sharesPerContract, expirationStyle, exerciseStyle, delivery }, bytes)

@[simp] theorem encode_length (message : SingleInstrumentDefinitionSnapshotV2Message) : (encode message).length = 273 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, InstrumentTradingStatus.encode_length, Alpha.encode_length, InstrumentType.encode_length, PutOrCall.encode_length, ExpirationStyle.encode_length, ExerciseStyle.encode_length, Delivery.encode_length]

theorem encode_length_pos (message : SingleInstrumentDefinitionSnapshotV2Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SingleInstrumentDefinitionSnapshotV2Message) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PutOrCall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ExpirationStyle.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseStyle.decode_encode, some_bind]
  dsimp only
  rw [Delivery.decode_encode, some_bind]
  rfl

end SingleInstrumentDefinitionSnapshotV2Message

/-- Multileg Definition Snapshot V 2 Message -/
structure MultilegDefinitionSnapshotV2Message where
  instrumentId : BitVec 32
  instrumentMessageNo : BitVec 64
  transactTime : BitVec 64
  tradingSessionDate : BitVec 16
  instrumentTradingStatus : InstrumentTradingStatus
  snapshotMessageInstructions : BitVec 16
  snapshotInstrumentsCount : BitVec 32
  lastIncrementalMessageSeq : BitVec 64
  spreadSymbol : Alpha 120
  description : Alpha 120
  instrumentType : InstrumentType
  maturityDate : BitVec 16
  firstTradingSessionDate : BitVec 16
  lastTradingSessionDate : BitVec 16
  expirationDate : BitVec 16
  cfiCode : Alpha 6
  currency : Alpha 3
  priceIncrement : BitVec 64
  priceMultiplier : BitVec 64
  strategyType : BitVec 8
  legsGroups : LegsGroups
  deriving DecidableEq, Repr

namespace MultilegDefinitionSnapshotV2Message

def encode (message : MultilegDefinitionSnapshotV2Message) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.instrumentMessageNo
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.tradingSessionDate
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (encodeUIntLE 2 message.snapshotMessageInstructions
    ++ (encodeUIntLE 4 message.snapshotInstrumentsCount
    ++ (encodeUIntLE 8 message.lastIncrementalMessageSeq
    ++ (Alpha.encode message.spreadSymbol
    ++ (Alpha.encode message.description
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (encodeUIntLE 2 message.firstTradingSessionDate
    ++ (encodeUIntLE 2 message.lastTradingSessionDate
    ++ (encodeUIntLE 2 message.expirationDate
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.currency
    ++ (encodeUIntLE 8 message.priceIncrement
    ++ (encodeUIntLE 8 message.priceMultiplier
    ++ (encodeUInt 1 message.strategyType
    ++ (LegsGroups.encode message.legsGroups))))))))))))))))))))

def decode (bytes : List UInt8) : Option (MultilegDefinitionSnapshotV2Message × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentMessageNo, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (snapshotMessageInstructions, bytes) ← decodeUIntLE 2 bytes
  let (snapshotInstrumentsCount, bytes) ← decodeUIntLE 4 bytes
  let (lastIncrementalMessageSeq, bytes) ← decodeUIntLE 8 bytes
  let (spreadSymbol, bytes) ← Alpha.decode 120 bytes
  let (description, bytes) ← Alpha.decode 120 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (firstTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (lastTradingSessionDate, bytes) ← decodeUIntLE 2 bytes
  let (expirationDate, bytes) ← decodeUIntLE 2 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (priceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (priceMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (strategyType, bytes) ← decodeUInt 1 bytes
  let (legsGroups, bytes) ← LegsGroups.decode bytes
  pure ({ instrumentId, instrumentMessageNo, transactTime, tradingSessionDate, instrumentTradingStatus, snapshotMessageInstructions, snapshotInstrumentsCount, lastIncrementalMessageSeq, spreadSymbol, description, instrumentType, maturityDate, firstTradingSessionDate, lastTradingSessionDate, expirationDate, cfiCode, currency, priceIncrement, priceMultiplier, strategyType, legsGroups }, bytes)

theorem encode_length_pos (message : MultilegDefinitionSnapshotV2Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultilegDefinitionSnapshotV2Message) : (encode message).length ≤ 12045 := by
  have bound_legsGroups := LegsGroups.encode_length_le message.legsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatus.encode_length, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MultilegDefinitionSnapshotV2Message) (rest : List UInt8) :
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
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LegsGroups.decode_encode, some_bind]
  rfl

end MultilegDefinitionSnapshotV2Message

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentTradingStatusIncrementalMessage (message : InstrumentTradingStatusIncrementalMessage) -- 3
  | tradesIncrementalMessage (message : TradesIncrementalMessage) -- 4
  | tradeCorrectMessage (message : TradeCorrectMessage) -- 5
  | tradeBustMessage (message : TradeBustMessage) -- 6
  | orderBookIncrementalMessage (message : OrderBookIncrementalMessage) -- 7
  | marketSummaryIncrementalMessage (message : MarketSummaryIncrementalMessage) -- 8
  | orderBookSnapshotMessage (message : OrderBookSnapshotMessage) -- 11
  | marketSummarySnapshotMessage (message : MarketSummarySnapshotMessage) -- 12
  | indexValueSnapshotMessage (message : IndexValueSnapshotMessage) -- 13
  | singleInstrumentDefinitionIncrementalV2Message (message : SingleInstrumentDefinitionIncrementalV2Message) -- 14
  | multilegDefinitionIncrementalV2Message (message : MultilegDefinitionIncrementalV2Message) -- 15
  | singleInstrumentDefinitionSnapshotV2Message (message : SingleInstrumentDefinitionSnapshotV2Message) -- 16
  | multilegDefinitionSnapshotV2Message (message : MultilegDefinitionSnapshotV2Message) -- 17
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .instrumentTradingStatusIncrementalMessage _ => 3
  | .tradesIncrementalMessage _ => 4
  | .tradeCorrectMessage _ => 5
  | .tradeBustMessage _ => 6
  | .orderBookIncrementalMessage _ => 7
  | .marketSummaryIncrementalMessage _ => 8
  | .orderBookSnapshotMessage _ => 11
  | .marketSummarySnapshotMessage _ => 12
  | .indexValueSnapshotMessage _ => 13
  | .singleInstrumentDefinitionIncrementalV2Message _ => 14
  | .multilegDefinitionIncrementalV2Message _ => 15
  | .singleInstrumentDefinitionSnapshotV2Message _ => 16
  | .multilegDefinitionSnapshotV2Message _ => 17

def encode : Payload → List UInt8
  | .instrumentTradingStatusIncrementalMessage message => InstrumentTradingStatusIncrementalMessage.encode message
  | .tradesIncrementalMessage message => TradesIncrementalMessage.encode message
  | .tradeCorrectMessage message => TradeCorrectMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .orderBookIncrementalMessage message => OrderBookIncrementalMessage.encode message
  | .marketSummaryIncrementalMessage message => MarketSummaryIncrementalMessage.encode message
  | .orderBookSnapshotMessage message => OrderBookSnapshotMessage.encode message
  | .marketSummarySnapshotMessage message => MarketSummarySnapshotMessage.encode message
  | .indexValueSnapshotMessage message => IndexValueSnapshotMessage.encode message
  | .singleInstrumentDefinitionIncrementalV2Message message => SingleInstrumentDefinitionIncrementalV2Message.encode message
  | .multilegDefinitionIncrementalV2Message message => MultilegDefinitionIncrementalV2Message.encode message
  | .singleInstrumentDefinitionSnapshotV2Message message => SingleInstrumentDefinitionSnapshotV2Message.encode message
  | .multilegDefinitionSnapshotV2Message message => MultilegDefinitionSnapshotV2Message.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 13320 := by
  cases message with
  | instrumentTradingStatusIncrementalMessage inner =>
    simp only [encode, InstrumentTradingStatusIncrementalMessage.encode_length]
    omega
  | tradesIncrementalMessage inner =>
    have bound_inner := TradesIncrementalMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeCorrectMessage inner =>
    have bound_inner := TradeCorrectMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeBustMessage inner =>
    have bound_inner := TradeBustMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderBookIncrementalMessage inner =>
    have bound_inner := OrderBookIncrementalMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketSummaryIncrementalMessage inner =>
    simp only [encode, MarketSummaryIncrementalMessage.encode_length]
    omega
  | orderBookSnapshotMessage inner =>
    have bound_inner := OrderBookSnapshotMessage.encode_length_le inner
    simp only [encode]
    omega
  | marketSummarySnapshotMessage inner =>
    simp only [encode, MarketSummarySnapshotMessage.encode_length]
    omega
  | indexValueSnapshotMessage inner =>
    simp only [encode, IndexValueSnapshotMessage.encode_length]
    omega
  | singleInstrumentDefinitionIncrementalV2Message inner =>
    simp only [encode, SingleInstrumentDefinitionIncrementalV2Message.encode_length]
    omega
  | multilegDefinitionIncrementalV2Message inner =>
    have bound_inner := MultilegDefinitionIncrementalV2Message.encode_length_le inner
    simp only [encode]
    omega
  | singleInstrumentDefinitionSnapshotV2Message inner =>
    simp only [encode, SingleInstrumentDefinitionSnapshotV2Message.encode_length]
    omega
  | multilegDefinitionSnapshotV2Message inner =>
    have bound_inner := MultilegDefinitionSnapshotV2Message.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 3 then (InstrumentTradingStatusIncrementalMessage.decode bytes).map fun (message, rest) => (.instrumentTradingStatusIncrementalMessage message, rest)
  else if tag = 4 then (TradesIncrementalMessage.decode bytes).map fun (message, rest) => (.tradesIncrementalMessage message, rest)
  else if tag = 5 then (TradeCorrectMessage.decode bytes).map fun (message, rest) => (.tradeCorrectMessage message, rest)
  else if tag = 6 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 7 then (OrderBookIncrementalMessage.decode bytes).map fun (message, rest) => (.orderBookIncrementalMessage message, rest)
  else if tag = 8 then (MarketSummaryIncrementalMessage.decode bytes).map fun (message, rest) => (.marketSummaryIncrementalMessage message, rest)
  else if tag = 11 then (OrderBookSnapshotMessage.decode bytes).map fun (message, rest) => (.orderBookSnapshotMessage message, rest)
  else if tag = 12 then (MarketSummarySnapshotMessage.decode bytes).map fun (message, rest) => (.marketSummarySnapshotMessage message, rest)
  else if tag = 13 then (IndexValueSnapshotMessage.decode bytes).map fun (message, rest) => (.indexValueSnapshotMessage message, rest)
  else if tag = 14 then (SingleInstrumentDefinitionIncrementalV2Message.decode bytes).map fun (message, rest) => (.singleInstrumentDefinitionIncrementalV2Message message, rest)
  else if tag = 15 then (MultilegDefinitionIncrementalV2Message.decode bytes).map fun (message, rest) => (.multilegDefinitionIncrementalV2Message message, rest)
  else if tag = 16 then (SingleInstrumentDefinitionSnapshotV2Message.decode bytes).map fun (message, rest) => (.singleInstrumentDefinitionSnapshotV2Message message, rest)
  else if tag = 17 then (MultilegDefinitionSnapshotV2Message.decode bytes).map fun (message, rest) => (.multilegDefinitionSnapshotV2Message message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Frame -/
structure SbeFrame where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeFrame

def encodeBody (message : SbeFrame) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decodeBody (bytes : List UInt8) : Option (SbeFrame × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : SbeFrame) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SbeFrame) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | instrumentTradingStatusIncrementalMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentTradingStatusIncrementalMessage.encode_length]
    omega
  | tradesIncrementalMessage inner =>
    have bound_inner := TradesIncrementalMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | tradeCorrectMessage inner =>
    have bound_inner := TradeCorrectMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | tradeBustMessage inner =>
    have bound_inner := TradeBustMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | orderBookIncrementalMessage inner =>
    have bound_inner := OrderBookIncrementalMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | marketSummaryIncrementalMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketSummaryIncrementalMessage.encode_length]
    omega
  | orderBookSnapshotMessage inner =>
    have bound_inner := OrderBookSnapshotMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | marketSummarySnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketSummarySnapshotMessage.encode_length]
    omega
  | indexValueSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexValueSnapshotMessage.encode_length]
    omega
  | singleInstrumentDefinitionIncrementalV2Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SingleInstrumentDefinitionIncrementalV2Message.encode_length]
    omega
  | multilegDefinitionIncrementalV2Message inner =>
    have bound_inner := MultilegDefinitionIncrementalV2Message.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | singleInstrumentDefinitionSnapshotV2Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SingleInstrumentDefinitionSnapshotV2Message.encode_length]
    omega
  | multilegDefinitionSnapshotV2Message inner =>
    have bound_inner := MultilegDefinitionSnapshotV2Message.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

/-- Size rule: Frame Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : SbeFrame → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (SbeFrame × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : SbeFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SbeFrame) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SbeFrame

/-- Packet -/
structure Packet where
  packetHeader : PacketHeader
  sbeFrame : List SbeFrame
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ (encodeMany SbeFrame.encode message.sbeFrame)

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let sbeFrame ← decodeAll SbeFrame.decode bytes.length bytes
  pure { packetHeader, sbeFrame }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [PacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany SbeFrame.encode SbeFrame.decode SbeFrame.decode_encode SbeFrame.encode_length_pos message.sbeFrame _ (encodeMany_length_ge SbeFrame.encode SbeFrame.encode_length_pos message.sbeFrame), some_bind]
  rfl

end Packet

end Omi.SmallxSmallfuturesOrderbookfeedSbeV22
