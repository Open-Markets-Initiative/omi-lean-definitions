import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Depth Of Market v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqPhlxoptionsDepthofmarketGlimpseV21Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4E, 0x4C, 0x45, 0x43, 0x57]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfOpeningProcess -- Start Of Opening Process
  | startOfNormalHoursClosingProcess -- Start Of Normal Hours Closing Process
  | startOfLateHoursClosingProcess -- Start Of Late Hours Closing Process
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | endOfWcoEarlyClosing -- End Of Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfOpeningProcess => 0x51
  | .startOfNormalHoursClosingProcess => 0x4E
  | .startOfLateHoursClosingProcess => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .endOfWcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x4E then .startOfNormalHoursClosingProcess
  else if byte = 0x4C then .startOfLateHoursClosingProcess
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else .endOfWcoEarlyClosing

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfOpeningProcess => decide
  | startOfNormalHoursClosingProcess => decide
  | startOfLateHoursClosingProcess => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | endOfWcoEarlyClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x4E]

inductive OptionType where
  | call -- Call
  | put -- Put
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .notApplicable

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Closing Type: one byte code -/
def ClosingType.codes : List UInt8 :=
  [0x4E, 0x4C, 0x57]

inductive ClosingType where
  | normalHours -- Normal Hours
  | lateHours -- Late Hours
  | wcoEarlyClosing -- Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingType

def toByte : ClosingType → UInt8
  | .normalHours => 0x4E
  | .lateHours => 0x4C
  | .wcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingType :=
  if byte = 0x4E then .normalHours
  else if byte = 0x4C then .lateHours
  else .wcoEarlyClosing

def ofByte (byte : UInt8) : ClosingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingType) : ofByte value.toByte = value := by
  cases value with
  | normalHours => decide
  | lateHours => decide
  | wcoEarlyClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClosingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingType

/-- Tradable: one byte code -/
def Tradable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Tradable where
  | tradable -- Tradable
  | notTradable -- Not Tradable
  | unlisted (byte : { byte : UInt8 // byte ∉ Tradable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tradable

def toByte : Tradable → UInt8
  | .tradable => 0x59
  | .notTradable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tradable :=
  if byte = 0x59 then .tradable
  else .notTradable

def ofByte (byte : UInt8) : Tradable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tradable) : ofByte value.toByte = value := by
  cases value with
  | tradable => decide
  | notTradable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tradable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tradable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tradable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tradable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tradable

/-- Mpv: one byte code -/
def Mpv.codes : List UInt8 :=
  [0x45, 0x53, 0x50]

inductive Mpv where
  | pennyEverywhere -- Penny Everywhere
  | scaled -- Scaled
  | pennyPilot -- Penny Pilot
  | unlisted (byte : { byte : UInt8 // byte ∉ Mpv.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Mpv

def toByte : Mpv → UInt8
  | .pennyEverywhere => 0x45
  | .scaled => 0x53
  | .pennyPilot => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Mpv :=
  if byte = 0x45 then .pennyEverywhere
  else if byte = 0x53 then .scaled
  else .pennyPilot

def ofByte (byte : UInt8) : Mpv :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Mpv) : ofByte value.toByte = value := by
  cases value with
  | pennyEverywhere => decide
  | scaled => decide
  | pennyPilot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Mpv) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Mpv × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Mpv) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Mpv) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Mpv

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x42, 0x53, 0x48, 0x54, 0x49, 0x4F, 0x52, 0x58]

inductive CurrentTradingState where
  | buySideSuspended -- Buy Side Suspended
  | sellSideSuspended -- Sell Side Suspended
  | haltInEffect -- Halt In Effect
  | continuousTrading -- Continuous Trading
  | preOpen -- Pre Open
  | openingAuction -- Opening Auction
  | reOpening -- Re Opening
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .buySideSuspended => 0x42
  | .sellSideSuspended => 0x53
  | .haltInEffect => 0x48
  | .continuousTrading => 0x54
  | .preOpen => 0x49
  | .openingAuction => 0x4F
  | .reOpening => 0x52
  | .closed => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x42 then .buySideSuspended
  else if byte = 0x53 then .sellSideSuspended
  else if byte = 0x48 then .haltInEffect
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x49 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x52 then .reOpening
  else .closed

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | buySideSuspended => decide
  | sellSideSuspended => decide
  | haltInEffect => decide
  | continuousTrading => decide
  | preOpen => decide
  | openingAuction => decide
  | reOpening => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentTradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentTradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentTradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CurrentTradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentTradingState

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x4D, 0x4E]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | buyImplied -- Buy Implied
  | sellImplied -- Sell Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .buyImplied => 0x4D
  | .sellImplied => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4D then .buyImplied
  else .sellImplied

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | buyImplied => decide
  | sellImplied => decide
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

/-- Order Capacity: one byte code -/
def OrderCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x42, 0x50, 0x4F, 0x4A, 0x20]

inductive OrderCapacity where
  | customerOrder -- Customer Order
  | firmOrder -- Firm Order
  | marketMakerOrder -- Market Maker Order
  | brokerDealerOrder -- Broker Dealer Order
  | professionalOrder -- Professional Order
  | otherExchangeMarketMakerOrder -- Other Exchange Market Maker Order
  | jointBackOffice -- Joint Back Office
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .customerOrder => 0x43
  | .firmOrder => 0x46
  | .marketMakerOrder => 0x4D
  | .brokerDealerOrder => 0x42
  | .professionalOrder => 0x50
  | .otherExchangeMarketMakerOrder => 0x4F
  | .jointBackOffice => 0x4A
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x43 then .customerOrder
  else if byte = 0x46 then .firmOrder
  else if byte = 0x4D then .marketMakerOrder
  else if byte = 0x42 then .brokerDealerOrder
  else if byte = 0x50 then .professionalOrder
  else if byte = 0x4F then .otherExchangeMarketMakerOrder
  else if byte = 0x4A then .jointBackOffice
  else .na

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | customerOrder => decide
  | firmOrder => decide
  | marketMakerOrder => decide
  | brokerDealerOrder => decide
  | professionalOrder => decide
  | otherExchangeMarketMakerOrder => decide
  | jointBackOffice => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCapacity

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

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

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Derivative Directory Message: 62 bytes -/
structure DerivativeDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  securitySymbol : Alpha 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : OptionType
  underlyingSymbol : Alpha 13
  closingType : ClosingType
  tradable : Tradable
  mpv : Mpv
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace DerivativeDirectoryMessage

def encode (message : DerivativeDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ClosingType.encode message.closingType
    ++ (Tradable.encode message.tradable
    ++ (Mpv.encode message.mpv
    ++ (Alpha.encode message.reserved16)))))))))))))

def decode (bytes : List UInt8) : Option (DerivativeDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (closingType, bytes) ← ClosingType.decode bytes
  let (tradable_, bytes) ← Tradable.decode bytes
  let (mpv, bytes) ← Mpv.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, instrumentId, securitySymbol, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, underlyingSymbol, closingType, tradable := tradable_, mpv, reserved16 }, bytes)

@[simp] theorem encode_length (message : DerivativeDirectoryMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, ClosingType.encode_length, Tradable.encode_length, Mpv.encode_length]

theorem encode_length_pos (message : DerivativeDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DerivativeDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClosingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tradable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Mpv.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DerivativeDirectoryMessage

/-- Trading Action Message: 15 bytes -/
structure TradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (CurrentTradingState.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ trackingNumber, timestamp, instrumentId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end TradingActionMessage

/-- Add Order Short Form Message: 32 bytes -/
structure AddOrderShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  orderCapacity : OrderCapacity
  priceShort : BitVec 16
  volumeShort : BitVec 16
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderShortFormMessage

def encode (message : AddOrderShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 2 message.priceShort
    ++ (encodeUInt 2 message.volumeShort
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (AddOrderShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  let (volumeShort, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, side, orderCapacity, priceShort, volumeShort, reserved4 }, bytes)

@[simp] theorem encode_length (message : AddOrderShortFormMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderShortFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderShortFormMessage

/-- Add Order Long Form Message: 36 bytes -/
structure AddOrderLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  orderReferenceNumber : BitVec 64
  side : Side
  orderCapacity : OrderCapacity
  priceLong : BitVec 32
  volumeLong : BitVec 32
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderLongFormMessage

def encode (message : AddOrderLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 4 message.priceLong
    ++ (encodeUInt 4 message.volumeLong
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (AddOrderLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (priceLong, bytes) ← decodeUInt 4 bytes
  let (volumeLong, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, orderReferenceNumber, side, orderCapacity, priceLong, volumeLong, reserved4 }, bytes)

@[simp] theorem encode_length (message : AddOrderLongFormMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderCapacity.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderLongFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderLongFormMessage

/-- Add Quote Short Form Message: 38 bytes -/
structure AddQuoteShortFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  askPriceShort : BitVec 16
  askSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace AddQuoteShortFormMessage

def encode (message : AddQuoteShortFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.askPriceShort
    ++ (encodeUInt 2 message.askSizeShort))))))))

def decode (bytes : List UInt8) : Option (AddQuoteShortFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (askPriceShort, bytes) ← decodeUInt 2 bytes
  let (askSizeShort, bytes) ← decodeUInt 2 bytes
  pure ({ trackingNumber, timestamp, instrumentId, bidReferenceNumber, askReferenceNumber, bidPriceShort, bidSizeShort, askPriceShort, askSizeShort }, bytes)

@[simp] theorem encode_length (message : AddQuoteShortFormMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteShortFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddQuoteShortFormMessage

/-- Add Quote Long Form Message: 46 bytes -/
structure AddQuoteLongFormMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  instrumentId : BitVec 32
  bidReferenceNumber : BitVec 64
  askReferenceNumber : BitVec 64
  bidPriceLong : BitVec 32
  bidSizeLong : BitVec 32
  askPriceLong : BitVec 32
  askSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace AddQuoteLongFormMessage

def encode (message : AddQuoteLongFormMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 8 message.bidReferenceNumber
    ++ (encodeUInt 8 message.askReferenceNumber
    ++ (encodeUInt 4 message.bidPriceLong
    ++ (encodeUInt 4 message.bidSizeLong
    ++ (encodeUInt 4 message.askPriceLong
    ++ (encodeUInt 4 message.askSizeLong))))))))

def decode (bytes : List UInt8) : Option (AddQuoteLongFormMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (bidReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (askReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (bidPriceLong, bytes) ← decodeUInt 4 bytes
  let (bidSizeLong, bytes) ← decodeUInt 4 bytes
  let (askPriceLong, bytes) ← decodeUInt 4 bytes
  let (askSizeLong, bytes) ← decodeUInt 4 bytes
  pure ({ trackingNumber, timestamp, instrumentId, bidReferenceNumber, askReferenceNumber, bidPriceLong, bidSizeLong, askPriceLong, askSizeLong }, bytes)

@[simp] theorem encode_length (message : AddQuoteLongFormMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AddQuoteLongFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddQuoteLongFormMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddQuoteLongFormMessage

/-- Snapshot Message: 20 bytes -/
structure SnapshotMessage where
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace SnapshotMessage

def encode (message : SnapshotMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (SnapshotMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : SnapshotMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SnapshotMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | derivativeDirectoryMessage (message : DerivativeDirectoryMessage) -- "m" 0x6D
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | addOrderShortFormMessage (message : AddOrderShortFormMessage) -- "r" 0x72
  | addOrderLongFormMessage (message : AddOrderLongFormMessage) -- "o" 0x6F
  | addQuoteShortFormMessage (message : AddQuoteShortFormMessage) -- "j" 0x6A
  | addQuoteLongFormMessage (message : AddQuoteLongFormMessage) -- "J" 0x4A
  | snapshotMessage (message : SnapshotMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .derivativeDirectoryMessage _ => 109
  | .tradingActionMessage _ => 72
  | .addOrderShortFormMessage _ => 114
  | .addOrderLongFormMessage _ => 111
  | .addQuoteShortFormMessage _ => 106
  | .addQuoteLongFormMessage _ => 74
  | .snapshotMessage _ => 77

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .derivativeDirectoryMessage message => DerivativeDirectoryMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .addOrderShortFormMessage message => AddOrderShortFormMessage.encode message
  | .addOrderLongFormMessage message => AddOrderLongFormMessage.encode message
  | .addQuoteShortFormMessage message => AddQuoteShortFormMessage.encode message
  | .addQuoteLongFormMessage message => AddQuoteLongFormMessage.encode message
  | .snapshotMessage message => SnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 62 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [encode, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
    omega
  | addOrderShortFormMessage inner =>
    simp only [encode, AddOrderShortFormMessage.encode_length]
    omega
  | addOrderLongFormMessage inner =>
    simp only [encode, AddOrderLongFormMessage.encode_length]
    omega
  | addQuoteShortFormMessage inner =>
    simp only [encode, AddQuoteShortFormMessage.encode_length]
    omega
  | addQuoteLongFormMessage inner =>
    simp only [encode, AddQuoteLongFormMessage.encode_length]
    omega
  | snapshotMessage inner =>
    simp only [encode, SnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 109 then (DerivativeDirectoryMessage.decode bytes).map fun (message, rest) => (.derivativeDirectoryMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 114 then (AddOrderShortFormMessage.decode bytes).map fun (message, rest) => (.addOrderShortFormMessage message, rest)
  else if tag = 111 then (AddOrderLongFormMessage.decode bytes).map fun (message, rest) => (.addOrderLongFormMessage message, rest)
  else if tag = 106 then (AddQuoteShortFormMessage.decode bytes).map fun (message, rest) => (.addQuoteShortFormMessage message, rest)
  else if tag = 74 then (AddQuoteLongFormMessage.decode bytes).map fun (message, rest) => (.addQuoteLongFormMessage message, rest)
  else if tag = 77 then (SnapshotMessage.decode bytes).map fun (message, rest) => (.snapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 63 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | derivativeDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, DerivativeDirectoryMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
    omega
  | addOrderShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderShortFormMessage.encode_length]
    omega
  | addOrderLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderLongFormMessage.encode_length]
    omega
  | addQuoteShortFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddQuoteShortFormMessage.encode_length]
    omega
  | addQuoteLongFormMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddQuoteLongFormMessage.encode_length]
    omega
  | snapshotMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 63 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqPhlxoptionsDepthofmarketGlimpseV21Server
