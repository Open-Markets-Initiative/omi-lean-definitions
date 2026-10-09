import Wire

/-!
# Tradelogiq Markets Inc. Lynx Tcp Level 2 v2.01

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TradelogiqLynxatsTcplevel2ItchV201Server

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
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43, 0x42, 0x52]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | tradingHalted -- Trading Halted
  | tradingResumed -- Trading Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .tradingHalted => 0x42
  | .tradingResumed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x42 then .tradingHalted
  else .tradingResumed

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | tradingHalted => decide
  | tradingResumed => decide
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

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x74, 0x76, 0x63, 0x71, 0x6F, 0x7A]

inductive Market where
  | tsx -- Tsx
  | tsxVenture -- Tsx Venture
  | cse -- Cse
  | nasdaqCanada -- Nasdaq Canada
  | omegaAts -- Omega Ats
  | cboeCanada -- Cboe Canada
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .tsx => 0x74
  | .tsxVenture => 0x76
  | .cse => 0x63
  | .nasdaqCanada => 0x71
  | .omegaAts => 0x6F
  | .cboeCanada => 0x7A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x74 then .tsx
  else if byte = 0x76 then .tsxVenture
  else if byte = 0x63 then .cse
  else if byte = 0x71 then .nasdaqCanada
  else if byte = 0x6F then .omegaAts
  else .cboeCanada

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxVenture => decide
  | cse => decide
  | nasdaqCanada => decide
  | omegaAts => decide
  | cboeCanada => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Market) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Market × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Market) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Market) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Market

/-- Shortable: one byte code -/
def Shortable.codes : List UInt8 :=
  [0x45, 0x53, 0x4E]

inductive Shortable where
  | shortExempt -- Short Exempt
  | shortable -- Shortable
  | notShortable -- Not Shortable
  | unlisted (byte : { byte : UInt8 // byte ∉ Shortable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Shortable

def toByte : Shortable → UInt8
  | .shortExempt => 0x45
  | .shortable => 0x53
  | .notShortable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Shortable :=
  if byte = 0x45 then .shortExempt
  else if byte = 0x53 then .shortable
  else .notShortable

def ofByte (byte : UInt8) : Shortable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Shortable) : ofByte value.toByte = value := by
  cases value with
  | shortExempt => decide
  | shortable => decide
  | notShortable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Shortable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Shortable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Shortable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Shortable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Shortable

/-- Dividend Indicator: one byte code -/
def DividendIndicator.codes : List UInt8 :=
  [0x41, 0x53, 0x51, 0x4D]

inductive DividendIndicator where
  | annual -- Annual
  | semiAnnual -- Semi Annual
  | quarterly -- Quarterly
  | monthly -- Monthly
  | unlisted (byte : { byte : UInt8 // byte ∉ DividendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DividendIndicator

def toByte : DividendIndicator → UInt8
  | .annual => 0x41
  | .semiAnnual => 0x53
  | .quarterly => 0x51
  | .monthly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DividendIndicator :=
  if byte = 0x41 then .annual
  else if byte = 0x53 then .semiAnnual
  else if byte = 0x51 then .quarterly
  else .monthly

def ofByte (byte : UInt8) : DividendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DividendIndicator) : ofByte value.toByte = value := by
  cases value with
  | annual => decide
  | semiAnnual => decide
  | quarterly => decide
  | monthly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DividendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DividendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DividendIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DividendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DividendIndicator

/-- Frequency: one byte code -/
def Frequency.codes : List UInt8 :=
  [0x41, 0x53, 0x51, 0x4D]

inductive Frequency where
  | annual -- Annual
  | semiAnnual -- Semi Annual
  | quarterly -- Quarterly
  | monthly -- Monthly
  | unlisted (byte : { byte : UInt8 // byte ∉ Frequency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Frequency

def toByte : Frequency → UInt8
  | .annual => 0x41
  | .semiAnnual => 0x53
  | .quarterly => 0x51
  | .monthly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Frequency :=
  if byte = 0x41 then .annual
  else if byte = 0x53 then .semiAnnual
  else if byte = 0x51 then .quarterly
  else .monthly

def ofByte (byte : UInt8) : Frequency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Frequency) : ofByte value.toByte = value := by
  cases value with
  | annual => decide
  | semiAnnual => decide
  | quarterly => decide
  | monthly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Frequency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Frequency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Frequency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Frequency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Frequency

/-- Security Type: one byte code -/
def SecurityType.codes : List UInt8 :=
  [0x62, 0x64, 0x72, 0x6E, 0x77]

inductive SecurityType where
  | bonds -- Bonds
  | debentures -- Debentures
  | rights -- Rights
  | notes -- Notes
  | warrants -- Warrants
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityType

def toByte : SecurityType → UInt8
  | .bonds => 0x62
  | .debentures => 0x64
  | .rights => 0x72
  | .notes => 0x6E
  | .warrants => 0x77
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityType :=
  if byte = 0x62 then .bonds
  else if byte = 0x64 then .debentures
  else if byte = 0x72 then .rights
  else if byte = 0x6E then .notes
  else .warrants

def ofByte (byte : UInt8) : SecurityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityType) : ofByte value.toByte = value := by
  cases value with
  | bonds => decide
  | debentures => decide
  | rights => decide
  | notes => decide
  | warrants => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityType

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive TradingState where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

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

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x44, 0x49, 0x4D, 0x4E]

inductive CrossType where
  | derivativesCross -- Derivatives Cross
  | internalCross -- Internal Cross
  | intentionalCross -- Intentional Cross
  | netAssetValueCross -- Net Asset Value Cross
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .derivativesCross => 0x44
  | .internalCross => 0x49
  | .intentionalCross => 0x4D
  | .netAssetValueCross => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x44 then .derivativesCross
  else if byte = 0x49 then .internalCross
  else if byte = 0x4D then .intentionalCross
  else .netAssetValueCross

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | derivativesCross => decide
  | internalCross => decide
  | intentionalCross => decide
  | netAssetValueCross => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Bypass where
  | bypass -- Bypass
  | nonBypass -- Non Bypass
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .bypass => 0x59
  | .nonBypass => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x59 then .bypass
  else .nonBypass

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | bypass => decide
  | nonBypass => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Bypass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Bypass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Bypass) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Bypass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Bypass

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive SettlementType where
  | regularSettlement -- Regular Settlement
  | cash -- Cash
  | nextDay -- Next Day
  | delayedDelivery -- Delayed Delivery
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .regularSettlement => 0x30
  | .cash => 0x31
  | .nextDay => 0x32
  | .delayedDelivery => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x30 then .regularSettlement
  else if byte = 0x31 then .cash
  else if byte = 0x32 then .nextDay
  else .delayedDelivery

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularSettlement => decide
  | cash => decide
  | nextDay => decide
  | delayedDelivery => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

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

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  reserved2 : Alpha 2
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.timestamp))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  pure ({ eventCode, reserved2, timestamp }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, EventCode.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 39 bytes -/
structure StockDirectoryMessage where
  market : Market
  stock : Alpha 10
  timestamp : BitVec 64
  boardLotSize : BitVec 32
  instrumentId : BitVec 16
  shortable : Shortable
  dividendIndicator : DividendIndicator
  reserved9 : Alpha 9
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  Market.encode message.market
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.boardLotSize
    ++ (encodeUInt 2 message.instrumentId
    ++ (Shortable.encode message.shortable
    ++ (DividendIndicator.encode message.dividendIndicator
    ++ (Alpha.encode message.reserved9
    ++ (Alpha.encode message.currency))))))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (market, bytes) ← Market.decode bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (boardLotSize, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (shortable_, bytes) ← Shortable.decode bytes
  let (dividendIndicator, bytes) ← DividendIndicator.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ market, stock, timestamp, boardLotSize, instrumentId, shortable := shortable_, dividendIndicator, reserved9, currency }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, Market.encode_length, Alpha.encode_length, encodeUInt_length, Shortable.encode_length, DividendIndicator.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Shortable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DividendIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Extended Stock Directory Message: 71 bytes -/
structure ExtendedStockDirectoryMessage where
  market : Market
  stock : Alpha 10
  timestamp : BitVec 64
  boardLotSize : BitVec 32
  instrumentId : BitVec 16
  shortable : Shortable
  frequency : Frequency
  reserved9 : Alpha 9
  currency : Alpha 3
  securityType : SecurityType
  expiryDate : Alpha 8
  description : Alpha 20
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace ExtendedStockDirectoryMessage

def encode (message : ExtendedStockDirectoryMessage) : List UInt8 :=
  Market.encode message.market
    ++ (Alpha.encode message.stock
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.boardLotSize
    ++ (encodeUInt 2 message.instrumentId
    ++ (Shortable.encode message.shortable
    ++ (Frequency.encode message.frequency
    ++ (Alpha.encode message.reserved9
    ++ (Alpha.encode message.currency
    ++ (SecurityType.encode message.securityType
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.description
    ++ (Alpha.encode message.reserved3))))))))))))

def decode (bytes : List UInt8) : Option (ExtendedStockDirectoryMessage × List UInt8) := do
  let (market, bytes) ← Market.decode bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (boardLotSize, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (shortable_, bytes) ← Shortable.decode bytes
  let (frequency, bytes) ← Frequency.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (securityType, bytes) ← SecurityType.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (description, bytes) ← Alpha.decode 20 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ market, stock, timestamp, boardLotSize, instrumentId, shortable := shortable_, frequency, reserved9, currency, securityType, expiryDate, description, reserved3 }, bytes)

@[simp] theorem encode_length (message : ExtendedStockDirectoryMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Market.encode_length, Alpha.encode_length, encodeUInt_length, Shortable.encode_length, Frequency.encode_length, SecurityType.encode_length]

theorem encode_length_pos (message : ExtendedStockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExtendedStockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Shortable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Frequency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExtendedStockDirectoryMessage

/-- Stock Trading Action Message: 15 bytes -/
structure StockTradingActionMessage where
  tradingState : TradingState
  instrumentId : BitVec 16
  timestamp : BitVec 64
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace StockTradingActionMessage

def encode (message : StockTradingActionMessage) : List UInt8 :=
  TradingState.encode message.tradingState
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.reason)))

def decode (bytes : List UInt8) : Option (StockTradingActionMessage × List UInt8) := do
  let (tradingState, bytes) ← TradingState.decode bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ tradingState, instrumentId, timestamp, reason }, bytes)

@[simp] theorem encode_length (message : StockTradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, TradingState.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : StockTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockTradingActionMessage

/-- Add Order Message: 27 bytes -/
structure AddOrderMessage where
  buySellIndicator : BuySellIndicator
  instrumentId : BitVec 16
  timestamp : BitVec 64
  orderReferenceNumber : BitVec 32
  shares : BitVec 32
  price : BitVec 32
  execBrokerId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderReferenceNumber
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.execBrokerId
    ++ (Alpha.encode message.reserved2)))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (execBrokerId, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ buySellIndicator, instrumentId, timestamp, orderReferenceNumber, shares, price, execBrokerId, reserved2 }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, BuySellIndicator.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 27 bytes -/
structure OrderExecutedMessage where
  marker : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  orderReferenceNumber : BitVec 32
  executedShares : BitVec 32
  matchNumber : BitVec 32
  contraBrokerId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.marker
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 2 message.contraBrokerId
    ++ (Alpha.encode message.reserved2)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (marker, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (contraBrokerId, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ marker, instrumentId, timestamp, orderReferenceNumber, executedShares, matchNumber, contraBrokerId, reserved2 }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 31 bytes -/
structure OrderExecutedWithPriceMessage where
  marker : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  orderReferenceNumber : BitVec 32
  executedShares : BitVec 32
  executionPrice : BitVec 32
  matchNumber : BitVec 32
  contraBrokerId : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  Alpha.encode message.marker
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedShares
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 2 message.contraBrokerId
    ++ (Alpha.encode message.reserved2))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (marker, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (executedShares, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (contraBrokerId, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ marker, instrumentId, timestamp, orderReferenceNumber, executedShares, executionPrice, matchNumber, contraBrokerId, reserved2 }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
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

end OrderExecutedWithPriceMessage

/-- Order Delete Message: 15 bytes -/
structure OrderDeleteMessage where
  reserved1 : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  orderReferenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderReferenceNumber)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, instrumentId, timestamp, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 27 bytes -/
structure OrderReplaceMessage where
  reserved1 : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  originalOrderReferenceNumber : BitVec 32
  newOrderReferenceNumber : BitVec 32
  shares : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.originalOrderReferenceNumber
    ++ (encodeUInt 4 message.newOrderReferenceNumber
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price))))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (originalOrderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (newOrderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, instrumentId, timestamp, originalOrderReferenceNumber, newOrderReferenceNumber, shares, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceMessage

/-- Order Cancel Message: 19 bytes -/
structure OrderCancelMessage where
  reserved1 : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  orderReferenceNumber : BitVec 32
  cancelledShares : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.orderReferenceNumber
    ++ (encodeUInt 4 message.cancelledShares))))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 4 bytes
  let (cancelledShares, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, instrumentId, timestamp, orderReferenceNumber, cancelledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelMessage

/-- Trade Message: 31 bytes -/
structure TradeMessage where
  side : Side
  instrumentId : BitVec 16
  timestamp : BitVec 64
  midpointBookTrade : BitVec 32
  shares : BitVec 32
  price : BitVec 32
  matchNumber : BitVec 32
  buyBrokerId : BitVec 16
  sellBrokerId : BitVec 16
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Side.encode message.side
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.midpointBookTrade
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 2 message.buyBrokerId
    ++ (encodeUInt 2 message.sellBrokerId))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (midpointBookTrade, bytes) ← decodeUInt 4 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (buyBrokerId, bytes) ← decodeUInt 2 bytes
  let (sellBrokerId, bytes) ← decodeUInt 2 bytes
  pure ({ side, instrumentId, timestamp, midpointBookTrade, shares, price, matchNumber, buyBrokerId, sellBrokerId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Side.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end TradeMessage

/-- Cross Trade Message: 31 bytes -/
structure CrossTradeMessage where
  crossType : CrossType
  instrumentId : BitVec 16
  timestamp : BitVec 64
  shares : BitVec 32
  price : BitVec 32
  matchNumber : BitVec 32
  buyBrokerId : BitVec 16
  sellBrokerId : BitVec 16
  bypass : Bypass
  settlementType : SettlementType
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace CrossTradeMessage

def encode (message : CrossTradeMessage) : List UInt8 :=
  CrossType.encode message.crossType
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.shares
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 2 message.buyBrokerId
    ++ (encodeUInt 2 message.sellBrokerId
    ++ (Bypass.encode message.bypass
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.reserved2))))))))))

def decode (bytes : List UInt8) : Option (CrossTradeMessage × List UInt8) := do
  let (crossType, bytes) ← CrossType.decode bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (shares, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (buyBrokerId, bytes) ← decodeUInt 2 bytes
  let (sellBrokerId, bytes) ← decodeUInt 2 bytes
  let (bypass_, bytes) ← Bypass.decode bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ crossType, instrumentId, timestamp, shares, price, matchNumber, buyBrokerId, sellBrokerId, bypass := bypass_, settlementType, reserved2 }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, CrossType.encode_length, encodeUInt_length, Bypass.encode_length, SettlementType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
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
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossTradeMessage

/-- Trade Bust Message: 15 bytes -/
structure TradeBustMessage where
  reserved1 : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.matchNumber)))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, instrumentId, timestamp, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeBustMessage

/-- Trade Amend Message: 39 bytes -/
structure TradeAmendMessage where
  reserved1 : Alpha 1
  instrumentId : BitVec 16
  timestamp : BitVec 64
  originalTradeId : BitVec 32
  originalTradePrice : BitVec 64
  originalTradeSize : BitVec 32
  correctedTradePrice : BitVec 64
  correctedTradeSize : BitVec 32
  deriving DecidableEq, Repr

namespace TradeAmendMessage

def encode (message : TradeAmendMessage) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.instrumentId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.originalTradeId
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeSize)))))))

def decode (bytes : List UInt8) : Option (TradeAmendMessage × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (instrumentId, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (originalTradeId, bytes) ← decodeUInt 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  pure ({ reserved1, instrumentId, timestamp, originalTradeId, originalTradePrice, originalTradeSize, correctedTradePrice, correctedTradeSize }, bytes)

@[simp] theorem encode_length (message : TradeAmendMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeAmendMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeAmendMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeAmendMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | extendedStockDirectoryMessage (message : ExtendedStockDirectoryMessage) -- "r" 0x72
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | crossTradeMessage (message : CrossTradeMessage) -- "Q" 0x51
  | tradeBustMessage (message : TradeBustMessage) -- "B" 0x42
  | tradeAmendMessage (message : TradeAmendMessage) -- "M" 0x4D
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .extendedStockDirectoryMessage _ => 114
  | .stockTradingActionMessage _ => 72
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .orderCancelMessage _ => 88
  | .tradeMessage _ => 80
  | .crossTradeMessage _ => 81
  | .tradeBustMessage _ => 66
  | .tradeAmendMessage _ => 77

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .extendedStockDirectoryMessage message => ExtendedStockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .tradeAmendMessage message => TradeAmendMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 71 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | extendedStockDirectoryMessage inner =>
    simp only [encode, ExtendedStockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [encode, StockTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [encode, CrossTradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [encode, TradeBustMessage.encode_length]
    omega
  | tradeAmendMessage inner =>
    simp only [encode, TradeAmendMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 114 then (ExtendedStockDirectoryMessage.decode bytes).map fun (message, rest) => (.extendedStockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
  else if tag = 66 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 77 then (TradeAmendMessage.decode bytes).map fun (message, rest) => (.tradeAmendMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  payload : Payload
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 72 := by
  unfold encode
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | extendedStockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExtendedStockDirectoryMessage.encode_length]
    omega
  | stockTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CrossTradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeBustMessage.encode_length]
    omega
  | tradeAmendMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeAmendMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .serverHeartbeat _ => 72
  | .sequencedDataPacket _ => 83

def encode : ServerPayload → List UInt8
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 72 := by
  cases message with
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Tcp Packet -/
structure ServerSoupTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupTcpPacket

def encodeBody (message : ServerSoupTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupTcpPacket : List ServerSoupTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupTcpPacket.encode message.serverSoupTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupTcpPacket ← decodeAll ServerSoupTcpPacket.decode bytes.length bytes
  pure { serverSoupTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupTcpPacket.encode ServerSoupTcpPacket.decode ServerSoupTcpPacket.decode_encode ServerSoupTcpPacket.encode_length_pos message.serverSoupTcpPacket _ (encodeMany_length_ge ServerSoupTcpPacket.encode ServerSoupTcpPacket.encode_length_pos message.serverSoupTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.TradelogiqLynxatsTcplevel2ItchV201Server
