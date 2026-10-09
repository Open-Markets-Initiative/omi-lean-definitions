import Wire

/-!
# Tradelogiq Markets Inc. Omega Snapshot Recovery v1.09

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TradelogiqOmegaatsSnapshotrecoveryItchV109Server

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

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | extendedStockDirectoryMessage (message : ExtendedStockDirectoryMessage) -- "r" 0x72
  | stockTradingActionMessage (message : StockTradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .extendedStockDirectoryMessage _ => 114
  | .stockTradingActionMessage _ => 72
  | .addOrderMessage _ => 65

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .extendedStockDirectoryMessage message => ExtendedStockDirectoryMessage.encode message
  | .stockTradingActionMessage message => StockTradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message

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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 114 then (ExtendedStockDirectoryMessage.decode bytes).map fun (message, rest) => (.extendedStockDirectoryMessage message, rest)
  else if tag = 72 then (StockTradingActionMessage.decode bytes).map fun (message, rest) => (.stockTradingActionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
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

end Omi.TradelogiqOmegaatsSnapshotrecoveryItchV109Server
