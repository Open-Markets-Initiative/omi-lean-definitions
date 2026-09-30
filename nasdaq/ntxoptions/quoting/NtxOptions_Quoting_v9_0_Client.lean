import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Specialized Quote Interface v9.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Client Soup Bin Tcp Packet's Packet Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNtxoptionsQuotingSqfV90Client

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

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x53, 0x43, 0x4F]

inductive InstrumentType where
  | simpleInstruments -- Simple Instruments
  | complexInstruments -- Complex Instruments
  | simpleInstrument -- Simple Instrument
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .simpleInstruments => 0x53
  | .complexInstruments => 0x43
  | .simpleInstrument => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x53 then .simpleInstruments
  else if byte = 0x43 then .complexInstruments
  else .simpleInstrument

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | simpleInstruments => decide
  | complexInstruments => decide
  | simpleInstrument => decide
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

/-- Reentry Indicator: one byte code -/
def ReentryIndicator.codes : List UInt8 :=
  [0x4E, 0x52]

inductive ReentryIndicator where
  | normal -- Normal
  | reentry -- Reentry
  | unlisted (byte : { byte : UInt8 // byte ∉ ReentryIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReentryIndicator

def toByte : ReentryIndicator → UInt8
  | .normal => 0x4E
  | .reentry => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReentryIndicator :=
  if byte = 0x4E then .normal
  else .reentry

def ofByte (byte : UInt8) : ReentryIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReentryIndicator) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | reentry => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReentryIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReentryIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReentryIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReentryIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReentryIndicator

/-- Stock Leg Short Sale: one byte code -/
def StockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive StockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ StockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockLegShortSale

def toByte : StockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : StockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockLegShortSale

/-- Msar Type: one byte code -/
def MsarType.codes : List UInt8 :=
  [0x41, 0x4D]

inductive MsarType where
  | auctionResponse -- Auction Response
  | marketSweep -- Market Sweep
  | unlisted (byte : { byte : UInt8 // byte ∉ MsarType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MsarType

def toByte : MsarType → UInt8
  | .auctionResponse => 0x41
  | .marketSweep => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MsarType :=
  if byte = 0x41 then .auctionResponse
  else .marketSweep

def ofByte (byte : UInt8) : MsarType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MsarType) : ofByte value.toByte = value := by
  cases value with
  | auctionResponse => decide
  | marketSweep => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MsarType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MsarType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MsarType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MsarType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MsarType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x2A, 0x54, 0x58, 0x59, 0x5A]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | notDisclosed -- Not Disclosed
  | buyShort -- Buy Short
  | buyShortExempt -- Buy Short Exempt
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notDisclosed => 0x2A
  | .buyShort => 0x54
  | .buyShortExempt => 0x58
  | .sellShort => 0x59
  | .sellShortExempt => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x2A then .notDisclosed
  else if byte = 0x54 then .buyShort
  else if byte = 0x58 then .buyShortExempt
  else if byte = 0x59 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notDisclosed => decide
  | buyShort => decide
  | buyShortExempt => decide
  | sellShort => decide
  | sellShortExempt => decide
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

/-- Debit Credit: one byte code -/
def DebitCredit.codes : List UInt8 :=
  [0x44, 0x43, 0x20]

inductive DebitCredit where
  | debit -- Debit
  | credit -- Credit
  | zero -- Zero
  | unlisted (byte : { byte : UInt8 // byte ∉ DebitCredit.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DebitCredit

def toByte : DebitCredit → UInt8
  | .debit => 0x44
  | .credit => 0x43
  | .zero => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DebitCredit :=
  if byte = 0x44 then .debit
  else if byte = 0x43 then .credit
  else .zero

def ofByte (byte : UInt8) : DebitCredit :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DebitCredit) : ofByte value.toByte = value := by
  cases value with
  | debit => decide
  | credit => decide
  | zero => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DebitCredit) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DebitCredit × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DebitCredit) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DebitCredit) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DebitCredit

/-- Price Protection: one byte code -/
def PriceProtection.codes : List UInt8 :=
  [0x4C, 0x4E]

inductive PriceProtection where
  | local_ -- Local
  | national -- National
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceProtection

def toByte : PriceProtection → UInt8
  | .local_ => 0x4C
  | .national => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceProtection :=
  if byte = 0x4C then .local_
  else .national

def ofByte (byte : UInt8) : PriceProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceProtection) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | national => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceProtection

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Request Packet: 51 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  heartbeatTimeout : Alpha 5
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber
    ++ (Alpha.encode message.heartbeatTimeout))))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  let (heartbeatTimeout, bytes) ← Alpha.decode 5 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber, heartbeatTimeout }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestPacket

/-- Notification Subscription Request Message: 36 bytes -/
structure NotificationSubscriptionRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  subscription : Alpha 24
  deriving DecidableEq, Repr

namespace NotificationSubscriptionRequestMessage

def encode (message : NotificationSubscriptionRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.subscription))

def decode (bytes : List UInt8) : Option (NotificationSubscriptionRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (subscription, bytes) ← Alpha.decode 24 bytes
  pure ({ badge, messageId, subscription }, bytes)

@[simp] theorem encode_length (message : NotificationSubscriptionRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NotificationSubscriptionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotificationSubscriptionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NotificationSubscriptionRequestMessage

/-- Complex Legs: 9 bytes -/
structure ComplexLegs where
  legInstrumentId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace ComplexLegs

def encode (message : ComplexLegs) : List UInt8 :=
  encodeUInt 4 message.legInstrumentId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio))

def decode (bytes : List UInt8) : Option (ComplexLegs × List UInt8) := do
  let (legInstrumentId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ legInstrumentId, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : ComplexLegs) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : ComplexLegs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexLegs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexLegs

/-- Add Complex Instrument Request Message -/
structure AddComplexInstrumentRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  complexLegs : Bounded 1 ComplexLegs
  deriving DecidableEq, Repr

namespace AddComplexInstrumentRequestMessage

def encode (message : AddComplexInstrumentRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.complexLegs.val.length)
    ++ (encodeMany ComplexLegs.encode message.complexLegs.val))))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (complexLegs_, bytes) ← decodeMany ComplexLegs.decode numberOfLegs.toNat bytes
  if fits_complexLegs : complexLegs_.length < 256 ^ 1 then
    pure ({ badge, messageId, underlyingSymbol, complexLegs := ⟨complexLegs_, fits_complexLegs⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrumentRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrumentRequestMessage) : (encode message).length ≤ 2321 := by
  have bound_complexLegs := message.complexLegs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const ComplexLegs.encode 9 ComplexLegs.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrumentRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ComplexLegs.encode ComplexLegs.decode ComplexLegs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexLegs.length_lt]
  rfl

end AddComplexInstrumentRequestMessage

/-- Mm Parameter Definition Request Message: 74 bytes -/
structure MmParameterDefinitionRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  instrumentType : InstrumentType
  underlying : Alpha 13
  interval : BitVec 16
  percentage : BitVec 16
  cumQty : BitVec 32
  delta : BitVec 32
  vega : BitVec 32
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace MmParameterDefinitionRequestMessage

def encode (message : MmParameterDefinitionRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (InstrumentType.encode message.instrumentType
    ++ (Alpha.encode message.underlying
    ++ (encodeUInt 2 message.interval
    ++ (encodeUInt 2 message.percentage
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 4 message.delta
    ++ (encodeUInt 4 message.vega
    ++ (Alpha.encode message.reserved32)))))))))

def decode (bytes : List UInt8) : Option (MmParameterDefinitionRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (underlying, bytes) ← Alpha.decode 13 bytes
  let (interval, bytes) ← decodeUInt 2 bytes
  let (percentage, bytes) ← decodeUInt 2 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (delta, bytes) ← decodeUInt 4 bytes
  let (vega, bytes) ← decodeUInt 4 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ badge, messageId, instrumentType, underlying, interval, percentage, cumQty, delta, vega, reserved32 }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionRequestMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, InstrumentType.encode_length]

theorem encode_length_pos (message : MmParameterDefinitionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmParameterDefinitionRequestMessage

/-- Active Qp Self Replenishment Set Limit Message: 29 bytes -/
structure ActiveQpSelfReplenishmentSetLimitMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  setValue : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveQpSelfReplenishmentSetLimitMessage

def encode (message : ActiveQpSelfReplenishmentSetLimitMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 4 message.setValue)))

def decode (bytes : List UInt8) : Option (ActiveQpSelfReplenishmentSetLimitMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (setValue, bytes) ← decodeUInt 4 bytes
  pure ({ badge, messageId, underlyingSymbol, setValue }, bytes)

@[simp] theorem encode_length (message : ActiveQpSelfReplenishmentSetLimitMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveQpSelfReplenishmentSetLimitMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveQpSelfReplenishmentSetLimitMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveQpSelfReplenishmentSetLimitMessage

/-- Rapid Fire Config Request Message: 25 bytes -/
structure RapidFireConfigRequestMessage where
  badge : Alpha 4
  underlyingSymbol : Alpha 13
  percentage : BitVec 16
  interval : BitVec 16
  cumQty : BitVec 32
  deriving DecidableEq, Repr

namespace RapidFireConfigRequestMessage

def encode (message : RapidFireConfigRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 2 message.percentage
    ++ (encodeUInt 2 message.interval
    ++ (encodeUInt 4 message.cumQty))))

def decode (bytes : List UInt8) : Option (RapidFireConfigRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (percentage, bytes) ← decodeUInt 2 bytes
  let (interval, bytes) ← decodeUInt 2 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  pure ({ badge, underlyingSymbol, percentage, interval, cumQty }, bytes)

@[simp] theorem encode_length (message : RapidFireConfigRequestMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RapidFireConfigRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RapidFireConfigRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RapidFireConfigRequestMessage

/-- Simple Quotes: 21 bytes -/
structure SimpleQuotes where
  instrumentId : BitVec 32
  bidPrice : BitVec 32
  bidSize : BitVec 32
  askPrice : BitVec 32
  askSize : BitVec 32
  reentryIndicator : ReentryIndicator
  deriving DecidableEq, Repr

namespace SimpleQuotes

def encode (message : SimpleQuotes) : List UInt8 :=
  encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (ReentryIndicator.encode message.reentryIndicator)))))

def decode (bytes : List UInt8) : Option (SimpleQuotes × List UInt8) := do
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (reentryIndicator, bytes) ← ReentryIndicator.decode bytes
  pure ({ instrumentId, bidPrice, bidSize, askPrice, askSize, reentryIndicator }, bytes)

@[simp] theorem encode_length (message : SimpleQuotes) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ReentryIndicator.encode_length]

theorem encode_length_pos (message : SimpleQuotes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuotes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReentryIndicator.decode_encode, some_bind]
  rfl

end SimpleQuotes

/-- Simple Quote Block Short Form Message -/
structure SimpleQuoteBlockShortFormMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  simpleQuotes : Bounded 2 SimpleQuotes
  deriving DecidableEq, Repr

namespace SimpleQuoteBlockShortFormMessage

def encode (message : SimpleQuoteBlockShortFormMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.simpleQuotes.val.length)
    ++ (encodeMany SimpleQuotes.encode message.simpleQuotes.val))))

def decode (bytes : List UInt8) : Option (SimpleQuoteBlockShortFormMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (simpleQuotes_, bytes) ← decodeMany SimpleQuotes.decode quoteCount.toNat bytes
  if fits_simpleQuotes : simpleQuotes_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, simpleQuotes := ⟨simpleQuotes_, fits_simpleQuotes⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleQuoteBlockShortFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleQuoteBlockShortFormMessage) : (encode message).length ≤ 1376257 := by
  have bound_simpleQuotes := message.simpleQuotes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SimpleQuotes.encode 21 SimpleQuotes.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleQuoteBlockShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SimpleQuotes.encode SimpleQuotes.decode SimpleQuotes.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.simpleQuotes.length_lt]
  rfl

end SimpleQuoteBlockShortFormMessage

/-- Simple Quote Block Short Form Detailed Message -/
structure SimpleQuoteBlockShortFormDetailedMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  simpleQuotes : Bounded 2 SimpleQuotes
  deriving DecidableEq, Repr

namespace SimpleQuoteBlockShortFormDetailedMessage

def encode (message : SimpleQuoteBlockShortFormDetailedMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.simpleQuotes.val.length)
    ++ (encodeMany SimpleQuotes.encode message.simpleQuotes.val))))

def decode (bytes : List UInt8) : Option (SimpleQuoteBlockShortFormDetailedMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (simpleQuotes_, bytes) ← decodeMany SimpleQuotes.decode quoteCount.toNat bytes
  if fits_simpleQuotes : simpleQuotes_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, simpleQuotes := ⟨simpleQuotes_, fits_simpleQuotes⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleQuoteBlockShortFormDetailedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleQuoteBlockShortFormDetailedMessage) : (encode message).length ≤ 1376257 := by
  have bound_simpleQuotes := message.simpleQuotes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SimpleQuotes.encode 21 SimpleQuotes.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleQuoteBlockShortFormDetailedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SimpleQuotes.encode SimpleQuotes.decode SimpleQuotes.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.simpleQuotes.length_lt]
  rfl

end SimpleQuoteBlockShortFormDetailedMessage

/-- Simple Quotes Long Form: 29 bytes -/
structure SimpleQuotesLongForm where
  quoteId : BitVec 64
  instrumentId : BitVec 32
  bidPrice : BitVec 32
  bidSize : BitVec 32
  askPrice : BitVec 32
  askSize : BitVec 32
  reentryIndicator : ReentryIndicator
  deriving DecidableEq, Repr

namespace SimpleQuotesLongForm

def encode (message : SimpleQuotesLongForm) : List UInt8 :=
  encodeUInt 8 message.quoteId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (ReentryIndicator.encode message.reentryIndicator))))))

def decode (bytes : List UInt8) : Option (SimpleQuotesLongForm × List UInt8) := do
  let (quoteId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (reentryIndicator, bytes) ← ReentryIndicator.decode bytes
  pure ({ quoteId, instrumentId, bidPrice, bidSize, askPrice, askSize, reentryIndicator }, bytes)

@[simp] theorem encode_length (message : SimpleQuotesLongForm) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ReentryIndicator.encode_length]

theorem encode_length_pos (message : SimpleQuotesLongForm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuotesLongForm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReentryIndicator.decode_encode, some_bind]
  rfl

end SimpleQuotesLongForm

/-- Simple Quote Block Long Form Message -/
structure SimpleQuoteBlockLongFormMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  simpleQuotesLongForm : Bounded 2 SimpleQuotesLongForm
  deriving DecidableEq, Repr

namespace SimpleQuoteBlockLongFormMessage

def encode (message : SimpleQuoteBlockLongFormMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.simpleQuotesLongForm.val.length)
    ++ (encodeMany SimpleQuotesLongForm.encode message.simpleQuotesLongForm.val))))

def decode (bytes : List UInt8) : Option (SimpleQuoteBlockLongFormMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (simpleQuotesLongForm_, bytes) ← decodeMany SimpleQuotesLongForm.decode quoteCount.toNat bytes
  if fits_simpleQuotesLongForm : simpleQuotesLongForm_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, simpleQuotesLongForm := ⟨simpleQuotesLongForm_, fits_simpleQuotesLongForm⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleQuoteBlockLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleQuoteBlockLongFormMessage) : (encode message).length ≤ 1900537 := by
  have bound_simpleQuotesLongForm := message.simpleQuotesLongForm.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SimpleQuotesLongForm.encode 29 SimpleQuotesLongForm.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleQuoteBlockLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SimpleQuotesLongForm.encode SimpleQuotesLongForm.decode SimpleQuotesLongForm.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.simpleQuotesLongForm.length_lt]
  rfl

end SimpleQuoteBlockLongFormMessage

/-- Simple Quote Block Long Form Detailed Message -/
structure SimpleQuoteBlockLongFormDetailedMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  simpleQuotesLongForm : Bounded 2 SimpleQuotesLongForm
  deriving DecidableEq, Repr

namespace SimpleQuoteBlockLongFormDetailedMessage

def encode (message : SimpleQuoteBlockLongFormDetailedMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.simpleQuotesLongForm.val.length)
    ++ (encodeMany SimpleQuotesLongForm.encode message.simpleQuotesLongForm.val))))

def decode (bytes : List UInt8) : Option (SimpleQuoteBlockLongFormDetailedMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (simpleQuotesLongForm_, bytes) ← decodeMany SimpleQuotesLongForm.decode quoteCount.toNat bytes
  if fits_simpleQuotesLongForm : simpleQuotesLongForm_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, simpleQuotesLongForm := ⟨simpleQuotesLongForm_, fits_simpleQuotesLongForm⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleQuoteBlockLongFormDetailedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleQuoteBlockLongFormDetailedMessage) : (encode message).length ≤ 1900537 := by
  have bound_simpleQuotesLongForm := message.simpleQuotesLongForm.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SimpleQuotesLongForm.encode 29 SimpleQuotesLongForm.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleQuoteBlockLongFormDetailedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SimpleQuotesLongForm.encode SimpleQuotesLongForm.decode SimpleQuotesLongForm.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.simpleQuotesLongForm.length_lt]
  rfl

end SimpleQuoteBlockLongFormDetailedMessage

/-- Complex Quotes: 34 bytes -/
structure ComplexQuotes where
  quoteId : BitVec 64
  instrumentId : BitVec 32
  bidPrice : BitVec 32
  bidSize : BitVec 32
  askPrice : BitVec 32
  askSize : BitVec 32
  reentryIndicator : ReentryIndicator
  stockLegShortSale : StockLegShortSale
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace ComplexQuotes

def encode (message : ComplexQuotes) : List UInt8 :=
  encodeUInt 8 message.quoteId
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (ReentryIndicator.encode message.reentryIndicator
    ++ (StockLegShortSale.encode message.stockLegShortSale
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (ComplexQuotes × List UInt8) := do
  let (quoteId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (reentryIndicator, bytes) ← ReentryIndicator.decode bytes
  let (stockLegShortSale, bytes) ← StockLegShortSale.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ quoteId, instrumentId, bidPrice, bidSize, askPrice, askSize, reentryIndicator, stockLegShortSale, reserved4 }, bytes)

@[simp] theorem encode_length (message : ComplexQuotes) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ReentryIndicator.encode_length, StockLegShortSale.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexQuotes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexQuotes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ReentryIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexQuotes

/-- Complex Quote Block Message -/
structure ComplexQuoteBlockMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  complexQuotes : Bounded 2 ComplexQuotes
  deriving DecidableEq, Repr

namespace ComplexQuoteBlockMessage

def encode (message : ComplexQuoteBlockMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.complexQuotes.val.length)
    ++ (encodeMany ComplexQuotes.encode message.complexQuotes.val))))

def decode (bytes : List UInt8) : Option (ComplexQuoteBlockMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (complexQuotes_, bytes) ← decodeMany ComplexQuotes.decode quoteCount.toNat bytes
  if fits_complexQuotes : complexQuotes_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, complexQuotes := ⟨complexQuotes_, fits_complexQuotes⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexQuoteBlockMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexQuoteBlockMessage) : (encode message).length ≤ 2228212 := by
  have bound_complexQuotes := message.complexQuotes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const ComplexQuotes.encode 34 ComplexQuotes.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexQuoteBlockMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 ComplexQuotes.encode ComplexQuotes.decode ComplexQuotes.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexQuotes.length_lt]
  rfl

end ComplexQuoteBlockMessage

/-- Complex Quote Block Detailed Message -/
structure ComplexQuoteBlockDetailedMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  complexQuotes : Bounded 2 ComplexQuotes
  deriving DecidableEq, Repr

namespace ComplexQuoteBlockDetailedMessage

def encode (message : ComplexQuoteBlockDetailedMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.complexQuotes.val.length)
    ++ (encodeMany ComplexQuotes.encode message.complexQuotes.val))))

def decode (bytes : List UInt8) : Option (ComplexQuoteBlockDetailedMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (quoteCount, bytes) ← decodeUInt 2 bytes
  let (complexQuotes_, bytes) ← decodeMany ComplexQuotes.decode quoteCount.toNat bytes
  if fits_complexQuotes : complexQuotes_.length < 256 ^ 2 then
    pure ({ badge, messageId, sentTimestamp, complexQuotes := ⟨complexQuotes_, fits_complexQuotes⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexQuoteBlockDetailedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexQuoteBlockDetailedMessage) : (encode message).length ≤ 2228212 := by
  have bound_complexQuotes := message.complexQuotes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const ComplexQuotes.encode 34 ComplexQuotes.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexQuoteBlockDetailedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 ComplexQuotes.encode ComplexQuotes.decode ComplexQuotes.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.complexQuotes.length_lt]
  rfl

end ComplexQuoteBlockDetailedMessage

/-- Underlying Purge Request Message: 34 bytes -/
structure UnderlyingPurgeRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  sentTimestamp : BitVec 64
  underlyingSymbol : Alpha 13
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace UnderlyingPurgeRequestMessage

def encode (message : UnderlyingPurgeRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 8 message.sentTimestamp
    ++ (Alpha.encode message.underlyingSymbol
    ++ (InstrumentType.encode message.instrumentType))))

def decode (bytes : List UInt8) : Option (UnderlyingPurgeRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (sentTimestamp, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ badge, messageId, sentTimestamp, underlyingSymbol, instrumentType }, bytes)

@[simp] theorem encode_length (message : UnderlyingPurgeRequestMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, InstrumentType.encode_length]

theorem encode_length_pos (message : UnderlyingPurgeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingPurgeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end UnderlyingPurgeRequestMessage

/-- Market Reentry Request Message: 26 bytes -/
structure MarketReentryRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  instrumentType : InstrumentType
  deriving DecidableEq, Repr

namespace MarketReentryRequestMessage

def encode (message : MarketReentryRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (InstrumentType.encode message.instrumentType)))

def decode (bytes : List UInt8) : Option (MarketReentryRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  pure ({ badge, messageId, underlyingSymbol, instrumentType }, bytes)

@[simp] theorem encode_length (message : MarketReentryRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, InstrumentType.encode_length]

theorem encode_length_pos (message : MarketReentryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketReentryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentType.decode_encode, some_bind]
  rfl

end MarketReentryRequestMessage

/-- Active Qp Self Replenishment Request Reentry Message: 29 bytes -/
structure ActiveQpSelfReplenishmentRequestReentryMessage where
  badge : Alpha 4
  messageId : BitVec 64
  underlyingSymbol : Alpha 13
  replenishmentValue : BitVec 32
  deriving DecidableEq, Repr

namespace ActiveQpSelfReplenishmentRequestReentryMessage

def encode (message : ActiveQpSelfReplenishmentRequestReentryMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 4 message.replenishmentValue)))

def decode (bytes : List UInt8) : Option (ActiveQpSelfReplenishmentRequestReentryMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (replenishmentValue, bytes) ← decodeUInt 4 bytes
  pure ({ badge, messageId, underlyingSymbol, replenishmentValue }, bytes)

@[simp] theorem encode_length (message : ActiveQpSelfReplenishmentRequestReentryMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ActiveQpSelfReplenishmentRequestReentryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActiveQpSelfReplenishmentRequestReentryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActiveQpSelfReplenishmentRequestReentryMessage

/-- Simple Msar Request Message: 30 bytes -/
structure SimpleMsarRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  msarType : MsarType
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  contracts : BitVec 32
  deriving DecidableEq, Repr

namespace SimpleMsarRequestMessage

def encode (message : SimpleMsarRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (MsarType.encode message.msarType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.contracts)))))))

def decode (bytes : List UInt8) : Option (SimpleMsarRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (msarType, bytes) ← MsarType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  pure ({ badge, messageId, instrumentId, msarType, auctionId, price, side, contracts }, bytes)

@[simp] theorem encode_length (message : SimpleMsarRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, MsarType.encode_length, Side.encode_length]

theorem encode_length_pos (message : SimpleMsarRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleMsarRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsarType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SimpleMsarRequestMessage

/-- Complex Msar Request Message: 36 bytes -/
structure ComplexMsarRequestMessage where
  badge : Alpha 4
  messageId : BitVec 64
  instrumentId : BitVec 32
  msarType : MsarType
  auctionId : BitVec 32
  price : BitVec 32
  side : Side
  debitCredit : DebitCredit
  contracts : BitVec 32
  priceProtection : PriceProtection
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace ComplexMsarRequestMessage

def encode (message : ComplexMsarRequestMessage) : List UInt8 :=
  Alpha.encode message.badge
    ++ (encodeUInt 8 message.messageId
    ++ (encodeUInt 4 message.instrumentId
    ++ (MsarType.encode message.msarType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.price
    ++ (Side.encode message.side
    ++ (DebitCredit.encode message.debitCredit
    ++ (encodeUInt 4 message.contracts
    ++ (PriceProtection.encode message.priceProtection
    ++ (Alpha.encode message.reserved4))))))))))

def decode (bytes : List UInt8) : Option (ComplexMsarRequestMessage × List UInt8) := do
  let (badge, bytes) ← Alpha.decode 4 bytes
  let (messageId, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (msarType, bytes) ← MsarType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (debitCredit, bytes) ← DebitCredit.decode bytes
  let (contracts, bytes) ← decodeUInt 4 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ badge, messageId, instrumentId, msarType, auctionId, price, side, debitCredit, contracts, priceProtection, reserved4 }, bytes)

@[simp] theorem encode_length (message : ComplexMsarRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, MsarType.encode_length, Side.encode_length, DebitCredit.encode_length, PriceProtection.encode_length]

theorem encode_length_pos (message : ComplexMsarRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexMsarRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsarType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DebitCredit.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexMsarRequestMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | notificationSubscriptionRequestMessage (message : NotificationSubscriptionRequestMessage) -- "AB" 0x4142
  | addComplexInstrumentRequestMessage (message : AddComplexInstrumentRequestMessage) -- "AC" 0x4143
  | mmParameterDefinitionRequestMessage (message : MmParameterDefinitionRequestMessage) -- "AE" 0x4145
  | activeQpSelfReplenishmentSetLimitMessage (message : ActiveQpSelfReplenishmentSetLimitMessage) -- "AG" 0x4147
  | rapidFireConfigRequestMessage (message : RapidFireConfigRequestMessage) -- "AF" 0x4146
  | simpleQuoteBlockShortFormMessage (message : SimpleQuoteBlockShortFormMessage) -- "QA" 0x5141
  | simpleQuoteBlockShortFormDetailedMessage (message : SimpleQuoteBlockShortFormDetailedMessage) -- "Qa" 0x5161
  | simpleQuoteBlockLongFormMessage (message : SimpleQuoteBlockLongFormMessage) -- "QM" 0x514D
  | simpleQuoteBlockLongFormDetailedMessage (message : SimpleQuoteBlockLongFormDetailedMessage) -- "Qm" 0x516D
  | complexQuoteBlockMessage (message : ComplexQuoteBlockMessage) -- "QD" 0x5144
  | complexQuoteBlockDetailedMessage (message : ComplexQuoteBlockDetailedMessage) -- "Qd" 0x5164
  | underlyingPurgeRequestMessage (message : UnderlyingPurgeRequestMessage) -- "Pu" 0x5075
  | marketReentryRequestMessage (message : MarketReentryRequestMessage) -- "RU" 0x5255
  | activeQpSelfReplenishmentRequestReentryMessage (message : ActiveQpSelfReplenishmentRequestReentryMessage) -- "RG" 0x5247
  | simpleMsarRequestMessage (message : SimpleMsarRequestMessage) -- "SB" 0x5342
  | complexMsarRequestMessage (message : ComplexMsarRequestMessage) -- "SX" 0x5358
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .notificationSubscriptionRequestMessage _ => 16706
  | .addComplexInstrumentRequestMessage _ => 16707
  | .mmParameterDefinitionRequestMessage _ => 16709
  | .activeQpSelfReplenishmentSetLimitMessage _ => 16711
  | .rapidFireConfigRequestMessage _ => 16710
  | .simpleQuoteBlockShortFormMessage _ => 20801
  | .simpleQuoteBlockShortFormDetailedMessage _ => 20833
  | .simpleQuoteBlockLongFormMessage _ => 20813
  | .simpleQuoteBlockLongFormDetailedMessage _ => 20845
  | .complexQuoteBlockMessage _ => 20804
  | .complexQuoteBlockDetailedMessage _ => 20836
  | .underlyingPurgeRequestMessage _ => 20597
  | .marketReentryRequestMessage _ => 21077
  | .activeQpSelfReplenishmentRequestReentryMessage _ => 21063
  | .simpleMsarRequestMessage _ => 21314
  | .complexMsarRequestMessage _ => 21336

def encode : UnsequencedMessage → List UInt8
  | .notificationSubscriptionRequestMessage message => NotificationSubscriptionRequestMessage.encode message
  | .addComplexInstrumentRequestMessage message => AddComplexInstrumentRequestMessage.encode message
  | .mmParameterDefinitionRequestMessage message => MmParameterDefinitionRequestMessage.encode message
  | .activeQpSelfReplenishmentSetLimitMessage message => ActiveQpSelfReplenishmentSetLimitMessage.encode message
  | .rapidFireConfigRequestMessage message => RapidFireConfigRequestMessage.encode message
  | .simpleQuoteBlockShortFormMessage message => SimpleQuoteBlockShortFormMessage.encode message
  | .simpleQuoteBlockShortFormDetailedMessage message => SimpleQuoteBlockShortFormDetailedMessage.encode message
  | .simpleQuoteBlockLongFormMessage message => SimpleQuoteBlockLongFormMessage.encode message
  | .simpleQuoteBlockLongFormDetailedMessage message => SimpleQuoteBlockLongFormDetailedMessage.encode message
  | .complexQuoteBlockMessage message => ComplexQuoteBlockMessage.encode message
  | .complexQuoteBlockDetailedMessage message => ComplexQuoteBlockDetailedMessage.encode message
  | .underlyingPurgeRequestMessage message => UnderlyingPurgeRequestMessage.encode message
  | .marketReentryRequestMessage message => MarketReentryRequestMessage.encode message
  | .activeQpSelfReplenishmentRequestReentryMessage message => ActiveQpSelfReplenishmentRequestReentryMessage.encode message
  | .simpleMsarRequestMessage message => SimpleMsarRequestMessage.encode message
  | .complexMsarRequestMessage message => ComplexMsarRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 2228212 := by
  cases message with
  | notificationSubscriptionRequestMessage inner =>
    simp only [encode, NotificationSubscriptionRequestMessage.encode_length]
    omega
  | addComplexInstrumentRequestMessage inner =>
    have bound_inner := AddComplexInstrumentRequestMessage.encode_length_le inner
    simp only [encode]
    omega
  | mmParameterDefinitionRequestMessage inner =>
    simp only [encode, MmParameterDefinitionRequestMessage.encode_length]
    omega
  | activeQpSelfReplenishmentSetLimitMessage inner =>
    simp only [encode, ActiveQpSelfReplenishmentSetLimitMessage.encode_length]
    omega
  | rapidFireConfigRequestMessage inner =>
    simp only [encode, RapidFireConfigRequestMessage.encode_length]
    omega
  | simpleQuoteBlockShortFormMessage inner =>
    have bound_inner := SimpleQuoteBlockShortFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | simpleQuoteBlockShortFormDetailedMessage inner =>
    have bound_inner := SimpleQuoteBlockShortFormDetailedMessage.encode_length_le inner
    simp only [encode]
    omega
  | simpleQuoteBlockLongFormMessage inner =>
    have bound_inner := SimpleQuoteBlockLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | simpleQuoteBlockLongFormDetailedMessage inner =>
    have bound_inner := SimpleQuoteBlockLongFormDetailedMessage.encode_length_le inner
    simp only [encode]
    omega
  | complexQuoteBlockMessage inner =>
    have bound_inner := ComplexQuoteBlockMessage.encode_length_le inner
    simp only [encode]
    omega
  | complexQuoteBlockDetailedMessage inner =>
    have bound_inner := ComplexQuoteBlockDetailedMessage.encode_length_le inner
    simp only [encode]
    omega
  | underlyingPurgeRequestMessage inner =>
    simp only [encode, UnderlyingPurgeRequestMessage.encode_length]
    omega
  | marketReentryRequestMessage inner =>
    simp only [encode, MarketReentryRequestMessage.encode_length]
    omega
  | activeQpSelfReplenishmentRequestReentryMessage inner =>
    simp only [encode, ActiveQpSelfReplenishmentRequestReentryMessage.encode_length]
    omega
  | simpleMsarRequestMessage inner =>
    simp only [encode, SimpleMsarRequestMessage.encode_length]
    omega
  | complexMsarRequestMessage inner =>
    simp only [encode, ComplexMsarRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 16706 then (NotificationSubscriptionRequestMessage.decode bytes).map fun (message, rest) => (.notificationSubscriptionRequestMessage message, rest)
  else if tag = 16707 then (AddComplexInstrumentRequestMessage.decode bytes).map fun (message, rest) => (.addComplexInstrumentRequestMessage message, rest)
  else if tag = 16709 then (MmParameterDefinitionRequestMessage.decode bytes).map fun (message, rest) => (.mmParameterDefinitionRequestMessage message, rest)
  else if tag = 16711 then (ActiveQpSelfReplenishmentSetLimitMessage.decode bytes).map fun (message, rest) => (.activeQpSelfReplenishmentSetLimitMessage message, rest)
  else if tag = 16710 then (RapidFireConfigRequestMessage.decode bytes).map fun (message, rest) => (.rapidFireConfigRequestMessage message, rest)
  else if tag = 20801 then (SimpleQuoteBlockShortFormMessage.decode bytes).map fun (message, rest) => (.simpleQuoteBlockShortFormMessage message, rest)
  else if tag = 20833 then (SimpleQuoteBlockShortFormDetailedMessage.decode bytes).map fun (message, rest) => (.simpleQuoteBlockShortFormDetailedMessage message, rest)
  else if tag = 20813 then (SimpleQuoteBlockLongFormMessage.decode bytes).map fun (message, rest) => (.simpleQuoteBlockLongFormMessage message, rest)
  else if tag = 20845 then (SimpleQuoteBlockLongFormDetailedMessage.decode bytes).map fun (message, rest) => (.simpleQuoteBlockLongFormDetailedMessage message, rest)
  else if tag = 20804 then (ComplexQuoteBlockMessage.decode bytes).map fun (message, rest) => (.complexQuoteBlockMessage message, rest)
  else if tag = 20836 then (ComplexQuoteBlockDetailedMessage.decode bytes).map fun (message, rest) => (.complexQuoteBlockDetailedMessage message, rest)
  else if tag = 20597 then (UnderlyingPurgeRequestMessage.decode bytes).map fun (message, rest) => (.underlyingPurgeRequestMessage message, rest)
  else if tag = 21077 then (MarketReentryRequestMessage.decode bytes).map fun (message, rest) => (.marketReentryRequestMessage message, rest)
  else if tag = 21063 then (ActiveQpSelfReplenishmentRequestReentryMessage.decode bytes).map fun (message, rest) => (.activeQpSelfReplenishmentRequestReentryMessage message, rest)
  else if tag = 21314 then (SimpleMsarRequestMessage.decode bytes).map fun (message, rest) => (.simpleMsarRequestMessage message, rest)
  else if tag = 21336 then (ComplexMsarRequestMessage.decode bytes).map fun (message, rest) => (.complexMsarRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 2228214 := by
  unfold encode
  cases message.unsequencedMessage with
  | notificationSubscriptionRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NotificationSubscriptionRequestMessage.encode_length]
    omega
  | addComplexInstrumentRequestMessage inner =>
    have bound_inner := AddComplexInstrumentRequestMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | mmParameterDefinitionRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MmParameterDefinitionRequestMessage.encode_length]
    omega
  | activeQpSelfReplenishmentSetLimitMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ActiveQpSelfReplenishmentSetLimitMessage.encode_length]
    omega
  | rapidFireConfigRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, RapidFireConfigRequestMessage.encode_length]
    omega
  | simpleQuoteBlockShortFormMessage inner =>
    have bound_inner := SimpleQuoteBlockShortFormMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | simpleQuoteBlockShortFormDetailedMessage inner =>
    have bound_inner := SimpleQuoteBlockShortFormDetailedMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | simpleQuoteBlockLongFormMessage inner =>
    have bound_inner := SimpleQuoteBlockLongFormMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | simpleQuoteBlockLongFormDetailedMessage inner =>
    have bound_inner := SimpleQuoteBlockLongFormDetailedMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | complexQuoteBlockMessage inner =>
    have bound_inner := ComplexQuoteBlockMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | complexQuoteBlockDetailedMessage inner =>
    have bound_inner := ComplexQuoteBlockDetailedMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | underlyingPurgeRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, UnderlyingPurgeRequestMessage.encode_length]
    omega
  | marketReentryRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MarketReentryRequestMessage.encode_length]
    omega
  | activeQpSelfReplenishmentRequestReentryMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ActiveQpSelfReplenishmentRequestReentryMessage.encode_length]
    omega
  | simpleMsarRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleMsarRequestMessage.encode_length]
    omega
  | complexMsarRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ComplexMsarRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat Packet: 0 bytes -/
structure ClientHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ClientHeartbeatPacket

def encode (_ : ClientHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeatPacket

/-- Logout Request Packet: 0 bytes -/
structure LogoutRequestPacket where
  deriving DecidableEq, Repr

namespace LogoutRequestPacket

def encode (_ : LogoutRequestPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequestPacket

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeatPacket (message : ClientHeartbeatPacket) -- "R" 0x52
  | logoutRequestPacket (message : LogoutRequestPacket) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeatPacket _ => 82
  | .logoutRequestPacket _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeatPacket message => ClientHeartbeatPacket.encode message
  | .logoutRequestPacket message => LogoutRequestPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 2228214 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeatPacket inner =>
    simp only [encode, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [encode, LogoutRequestPacket.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeatPacket.decode bytes).map fun (message, rest) => (.clientHeartbeatPacket message, rest)
  else if tag = 79 then (LogoutRequestPacket.decode bytes).map fun (message, rest) => (.logoutRequestPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNtxoptionsQuotingSqfV90Client
