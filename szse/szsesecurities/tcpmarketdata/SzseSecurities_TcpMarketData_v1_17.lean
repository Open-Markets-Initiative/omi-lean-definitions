import Wire

/-!
# Shenzhen Stock Exchange Szse Tcp Market Data v1.17

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SzseSzsesecuritiesTcpmarketdataSzsebinaryV117

/-- Amounts Status: one byte code -/
def AmountsStatus.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive AmountsStatus where
  | quotaUnavailable -- Quota Unavailable
  | quotaAvailable -- Quota Available
  | quotaAdequate -- Quota Adequate
  | unlisted (byte : { byte : UInt8 // byte ∉ AmountsStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AmountsStatus

def toByte : AmountsStatus → UInt8
  | .quotaUnavailable => 0x31
  | .quotaAvailable => 0x32
  | .quotaAdequate => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AmountsStatus :=
  if byte = 0x31 then .quotaUnavailable
  else if byte = 0x32 then .quotaAvailable
  else .quotaAdequate

def ofByte (byte : UInt8) : AmountsStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AmountsStatus) : ofByte value.toByte = value := by
  cases value with
  | quotaUnavailable => decide
  | quotaAvailable => decide
  | quotaAdequate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AmountsStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AmountsStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AmountsStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AmountsStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AmountsStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AmountsStatus

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x47, 0x46]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | borrow -- Borrow
  | lend -- Lend
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .borrow => 0x47
  | .lend => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x47 then .borrow
  else .lend

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | borrow => decide
  | lend => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Ord Type: one byte code -/
def OrdType.codes : List UInt8 :=
  [0x31, 0x32, 0x55]

inductive OrdType where
  | marketPrice -- Market Price
  | limitPrice -- Limit Price
  | bestPriceOfThisParty -- Best Price Of This Party
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .marketPrice => 0x31
  | .limitPrice => 0x32
  | .bestPriceOfThisParty => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .marketPrice
  else if byte = 0x32 then .limitPrice
  else .bestPriceOfThisParty

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | marketPrice => decide
  | limitPrice => decide
  | bestPriceOfThisParty => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdType

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x34, 0x46]

inductive ExecType where
  | cancelled -- Cancelled
  | traded -- Traded
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .cancelled => 0x34
  | .traded => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x34 then .cancelled
  else .traded

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | cancelled => decide
  | traded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Logon Message: 92 bytes -/
structure LogonMessage where
  senderCompId : Alpha 20
  targetCompId : Alpha 20
  heartBtInt : BitVec 32
  password : Alpha 16
  defaultApplVerId : Alpha 32
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.senderCompId
    ++ (Alpha.encode message.targetCompId
    ++ (encodeUInt 4 message.heartBtInt
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.defaultApplVerId))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (senderCompId, bytes) ← Alpha.decode 20 bytes
  let (targetCompId, bytes) ← Alpha.decode 20 bytes
  let (heartBtInt, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (defaultApplVerId, bytes) ← Alpha.decode 32 bytes
  pure ({ senderCompId, targetCompId, heartBtInt, password, defaultApplVerId }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logout Message: 204 bytes -/
structure LogoutMessage where
  sessionStatus : BitVec 32
  text : Alpha 200
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 4 message.sessionStatus
    ++ (Alpha.encode message.text)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 4 bytes
  let (text, bytes) ← Alpha.decode 200 bytes
  pure ({ sessionStatus, text }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Channel Heartbeat Message: 12 bytes -/
structure ChannelHeartbeatMessage where
  channelNo : BitVec 16
  applLastSeqNum : BitVec 64
  endOfChannel : BitVec 16
  deriving DecidableEq, Repr

namespace ChannelHeartbeatMessage

def encode (message : ChannelHeartbeatMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applLastSeqNum
    ++ (encodeUInt 2 message.endOfChannel))

def decode (bytes : List UInt8) : Option (ChannelHeartbeatMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applLastSeqNum, bytes) ← decodeUInt 8 bytes
  let (endOfChannel, bytes) ← decodeUInt 2 bytes
  pure ({ channelNo, applLastSeqNum, endOfChannel }, bytes)

@[simp] theorem encode_length (message : ChannelHeartbeatMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ChannelHeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelHeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ChannelHeartbeatMessage

/-- Retransmitting Message: 44 bytes -/
structure RetransmittingMessage where
  resendType : BitVec 8
  channelNo : BitVec 16
  applBegSeqNum : BitVec 64
  applEndSeqNum : BitVec 64
  newsId : Alpha 8
  resendStatus : BitVec 8
  rejectText : Alpha 16
  deriving DecidableEq, Repr

namespace RetransmittingMessage

def encode (message : RetransmittingMessage) : List UInt8 :=
  encodeUInt 1 message.resendType
    ++ (encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applBegSeqNum
    ++ (encodeUInt 8 message.applEndSeqNum
    ++ (Alpha.encode message.newsId
    ++ (encodeUInt 1 message.resendStatus
    ++ (Alpha.encode message.rejectText))))))

def decode (bytes : List UInt8) : Option (RetransmittingMessage × List UInt8) := do
  let (resendType, bytes) ← decodeUInt 1 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applBegSeqNum, bytes) ← decodeUInt 8 bytes
  let (applEndSeqNum, bytes) ← decodeUInt 8 bytes
  let (newsId, bytes) ← Alpha.decode 8 bytes
  let (resendStatus, bytes) ← decodeUInt 1 bytes
  let (rejectText, bytes) ← Alpha.decode 16 bytes
  pure ({ resendType, channelNo, applBegSeqNum, applEndSeqNum, newsId, resendStatus, rejectText }, bytes)

@[simp] theorem encode_length (message : RetransmittingMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmittingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmittingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmittingMessage

/-- Client User Information Reporting Message: 26 bytes -/
structure ClientUserInformationReportingMessage where
  origTime : BitVec 64
  versionCode : Alpha 16
  userNum : BitVec 16
  deriving DecidableEq, Repr

namespace ClientUserInformationReportingMessage

def encode (message : ClientUserInformationReportingMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (Alpha.encode message.versionCode
    ++ (encodeUInt 2 message.userNum))

def decode (bytes : List UInt8) : Option (ClientUserInformationReportingMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (versionCode, bytes) ← Alpha.decode 16 bytes
  let (userNum, bytes) ← decodeUInt 2 bytes
  pure ({ origTime, versionCode, userNum }, bytes)

@[simp] theorem encode_length (message : ClientUserInformationReportingMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ClientUserInformationReportingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientUserInformationReportingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClientUserInformationReportingMessage

/-- Md Stream I Ds: 15 bytes -/
structure MdStreamIDs where
  mdStreamId : Alpha 3
  stockNum : BitVec 32
  tradingPhaseCode : Alpha 8
  deriving DecidableEq, Repr

namespace MdStreamIDs

def encode (message : MdStreamIDs) : List UInt8 :=
  Alpha.encode message.mdStreamId
    ++ (encodeUInt 4 message.stockNum
    ++ (Alpha.encode message.tradingPhaseCode))

def decode (bytes : List UInt8) : Option (MdStreamIDs × List UInt8) := do
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (stockNum, bytes) ← decodeUInt 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  pure ({ mdStreamId, stockNum, tradingPhaseCode }, bytes)

@[simp] theorem encode_length (message : MdStreamIDs) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MdStreamIDs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdStreamIDs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MdStreamIDs

/-- Statistics Of Snapshot Data Channel Message -/
structure StatisticsOfSnapshotDataChannelMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamIDs : Bounded 4 MdStreamIDs
  deriving DecidableEq, Repr

namespace StatisticsOfSnapshotDataChannelMessage

def encode (message : StatisticsOfSnapshotDataChannelMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdStreamIDs.val.length)
    ++ (encodeMany MdStreamIDs.encode message.mdStreamIDs.val)))

def decode (bytes : List UInt8) : Option (StatisticsOfSnapshotDataChannelMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (noMdStreamId, bytes) ← decodeUInt 4 bytes
  let (mdStreamIDs_, bytes) ← decodeMany MdStreamIDs.decode noMdStreamId.toNat bytes
  if fits_mdStreamIDs : mdStreamIDs_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamIDs := ⟨mdStreamIDs_, fits_mdStreamIDs⟩ }, bytes)
  else none

theorem encode_length_pos (message : StatisticsOfSnapshotDataChannelMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StatisticsOfSnapshotDataChannelMessage) : (encode message).length ≤ 64424509439 := by
  have bound_mdStreamIDs := message.mdStreamIDs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const MdStreamIDs.encode 15 MdStreamIDs.encode_length]
  omega

@[simp] theorem decode_encode (message : StatisticsOfSnapshotDataChannelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 MdStreamIDs.encode MdStreamIDs.decode MdStreamIDs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdStreamIDs.length_lt]
  rfl

end StatisticsOfSnapshotDataChannelMessage

/-- Business Reject Message: 74 bytes -/
structure BusinessRejectMessage where
  refSeqNum : BitVec 64
  refMsgType : BitVec 32
  businessRejectRefId : Alpha 10
  businessRejectReason : BitVec 16
  businessRejectText : Alpha 50
  deriving DecidableEq, Repr

namespace BusinessRejectMessage

def encode (message : BusinessRejectMessage) : List UInt8 :=
  encodeUInt 8 message.refSeqNum
    ++ (encodeUInt 4 message.refMsgType
    ++ (Alpha.encode message.businessRejectRefId
    ++ (encodeUInt 2 message.businessRejectReason
    ++ (Alpha.encode message.businessRejectText))))

def decode (bytes : List UInt8) : Option (BusinessRejectMessage × List UInt8) := do
  let (refSeqNum, bytes) ← decodeUInt 8 bytes
  let (refMsgType, bytes) ← decodeUInt 4 bytes
  let (businessRejectRefId, bytes) ← Alpha.decode 10 bytes
  let (businessRejectReason, bytes) ← decodeUInt 2 bytes
  let (businessRejectText, bytes) ← Alpha.decode 50 bytes
  pure ({ refSeqNum, refMsgType, businessRejectRefId, businessRejectReason, businessRejectText }, bytes)

@[simp] theorem encode_length (message : BusinessRejectMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BusinessRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessRejectMessage

/-- Real Time Market Status Message: 69 bytes -/
structure RealTimeMarketStatusMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  marketId : Alpha 8
  marketSegmentId : Alpha 8
  tradingSessionId : Alpha 4
  tradingSessionSubId : Alpha 4
  tradSesStatus : BitVec 16
  tradSesStartTime : BitVec 64
  tradSesEndTime : BitVec 64
  thredholdAmount : BitVec 64
  posAmt : BitVec 64
  amountsStatus : AmountsStatus
  deriving DecidableEq, Repr

namespace RealTimeMarketStatusMessage

def encode (message : RealTimeMarketStatusMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (Alpha.encode message.tradingSessionId
    ++ (Alpha.encode message.tradingSessionSubId
    ++ (encodeUInt 2 message.tradSesStatus
    ++ (encodeUInt 8 message.tradSesStartTime
    ++ (encodeUInt 8 message.tradSesEndTime
    ++ (encodeUInt 8 message.thredholdAmount
    ++ (encodeUInt 8 message.posAmt
    ++ (AmountsStatus.encode message.amountsStatus)))))))))))

def decode (bytes : List UInt8) : Option (RealTimeMarketStatusMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (marketId, bytes) ← Alpha.decode 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 8 bytes
  let (tradingSessionId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionSubId, bytes) ← Alpha.decode 4 bytes
  let (tradSesStatus, bytes) ← decodeUInt 2 bytes
  let (tradSesStartTime, bytes) ← decodeUInt 8 bytes
  let (tradSesEndTime, bytes) ← decodeUInt 8 bytes
  let (thredholdAmount, bytes) ← decodeUInt 8 bytes
  let (posAmt, bytes) ← decodeUInt 8 bytes
  let (amountsStatus, bytes) ← AmountsStatus.decode bytes
  pure ({ origTime, channelNo, marketId, marketSegmentId, tradingSessionId, tradingSessionSubId, tradSesStatus, tradSesStartTime, tradSesEndTime, thredholdAmount, posAmt, amountsStatus }, bytes)

@[simp] theorem encode_length (message : RealTimeMarketStatusMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, AmountsStatus.encode_length]

theorem encode_length_pos (message : RealTimeMarketStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RealTimeMarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [AmountsStatus.decode_encode, some_bind]
  rfl

end RealTimeMarketStatusMessage

/-- Switch: 4 bytes -/
structure Switch where
  securitySwitchType : BitVec 16
  securitySwitchStatus : BitVec 16
  deriving DecidableEq, Repr

namespace Switch

def encode (message : Switch) : List UInt8 :=
  encodeUInt 2 message.securitySwitchType
    ++ (encodeUInt 2 message.securitySwitchStatus)

def decode (bytes : List UInt8) : Option (Switch × List UInt8) := do
  let (securitySwitchType, bytes) ← decodeUInt 2 bytes
  let (securitySwitchStatus, bytes) ← decodeUInt 2 bytes
  pure ({ securitySwitchType, securitySwitchStatus }, bytes)

@[simp] theorem encode_length (message : Switch) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Switch) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Switch) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Switch

/-- Real Time Status Of Security Message -/
structure RealTimeStatusOfSecurityMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  securityId : Alpha 8
  securityIdSource : Alpha 4
  financialStatus : Alpha 8
  switch : Bounded 4 Switch
  deriving DecidableEq, Repr

namespace RealTimeStatusOfSecurityMessage

def encode (message : RealTimeStatusOfSecurityMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.financialStatus
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.switch.val.length)
    ++ (encodeMany Switch.encode message.switch.val))))))

def decode (bytes : List UInt8) : Option (RealTimeStatusOfSecurityMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (financialStatus, bytes) ← Alpha.decode 8 bytes
  let (noSwitch, bytes) ← decodeUInt 4 bytes
  let (switch_, bytes) ← decodeMany Switch.decode noSwitch.toNat bytes
  if fits_switch : switch_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, securityId, securityIdSource, financialStatus, switch := ⟨switch_, fits_switch⟩ }, bytes)
  else none

theorem encode_length_pos (message : RealTimeStatusOfSecurityMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RealTimeStatusOfSecurityMessage) : (encode message).length ≤ 17179869214 := by
  have bound_switch := message.switch.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const Switch.encode 4 Switch.encode_length]
  omega

@[simp] theorem decode_encode (message : RealTimeStatusOfSecurityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 Switch.encode Switch.decode Switch.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.switch.length_lt]
  rfl

end RealTimeStatusOfSecurityMessage

/-- Announcements Message -/
structure AnnouncementsMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  newsId : Alpha 8
  headline : Alpha 128
  rawDataFormat : Alpha 8
  rawData : Bounded 4 UInt8
  deriving DecidableEq, Repr

namespace AnnouncementsMessage

def encode (message : AnnouncementsMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.newsId
    ++ (Alpha.encode message.headline
    ++ (Alpha.encode message.rawDataFormat
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.rawData.val.length)
    ++ (encodeMany Byte.encode message.rawData.val))))))

def decode (bytes : List UInt8) : Option (AnnouncementsMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (newsId, bytes) ← Alpha.decode 8 bytes
  let (headline, bytes) ← Alpha.decode 128 bytes
  let (rawDataFormat, bytes) ← Alpha.decode 8 bytes
  let (rawDataLength, bytes) ← decodeUInt 4 bytes
  let (rawData_, bytes) ← decodeMany Byte.decode rawDataLength.toNat bytes
  if fits_rawData : rawData_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, newsId, headline, rawDataFormat, rawData := ⟨rawData_, fits_rawData⟩ }, bytes)
  else none

theorem encode_length_pos (message : AnnouncementsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AnnouncementsMessage) : (encode message).length ≤ 4294967453 := by
  have bound_rawData := message.rawData.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : AnnouncementsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.rawData.length_lt]
  rfl

end AnnouncementsMessage

/-- Orders: 8 bytes -/
structure Orders where
  orderQty : BitVec 64
  deriving DecidableEq, Repr

namespace Orders

def encode (message : Orders) : List UInt8 :=
  encodeUInt 8 message.orderQty

def decode (bytes : List UInt8) : Option (Orders × List UInt8) := do
  let (orderQty, bytes) ← decodeUInt 8 bytes
  pure ({ orderQty }, bytes)

@[simp] theorem encode_length (message : Orders) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : Orders) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Orders) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Orders

/-- Md Entries -/
structure MdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdPriceLevel : BitVec 16
  numberOfOrders : BitVec 64
  orders : Bounded 4 Orders
  deriving DecidableEq, Repr

namespace MdEntries

def encode (message : MdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx
    ++ (encodeUInt 8 message.mdEntrySize
    ++ (encodeUInt 2 message.mdPriceLevel
    ++ (encodeUInt 8 message.numberOfOrders
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.orders.val.length)
    ++ (encodeMany Orders.encode message.orders.val))))))

def decode (bytes : List UInt8) : Option (MdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  let (mdEntrySize, bytes) ← decodeUInt 8 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 2 bytes
  let (numberOfOrders, bytes) ← decodeUInt 8 bytes
  let (noOrders, bytes) ← decodeUInt 4 bytes
  let (orders_, bytes) ← decodeMany Orders.decode noOrders.toNat bytes
  if fits_orders : orders_.length < 256 ^ 4 then
    pure ({ mdEntryType, mdEntryPx, mdEntrySize, mdPriceLevel, numberOfOrders, orders := ⟨orders_, fits_orders⟩ }, bytes)
  else none

theorem encode_length_pos (message : MdEntries) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdEntries) : (encode message).length ≤ 34359738392 := by
  have bound_orders := message.orders.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const Orders.encode 8 Orders.encode_length]
  omega

@[simp] theorem decode_encode (message : MdEntries) (rest : List UInt8) :
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
  rw [decodeMany_bounded 4 Orders.encode Orders.decode Orders.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orders.length_lt]
  rfl

end MdEntries

/-- Snapshot Data Of Cash Auction Message -/
structure SnapshotDataOfCashAuctionMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  mdEntries : Bounded 4 MdEntries
  deriving DecidableEq, Repr

namespace SnapshotDataOfCashAuctionMessage

def encode (message : SnapshotDataOfCashAuctionMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdEntries.val.length)
    ++ (encodeMany MdEntries.encode message.mdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (SnapshotDataOfCashAuctionMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (mdEntries_, bytes) ← decodeMany MdEntries.decode noMdEntries.toNat bytes
  if fits_mdEntries : mdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, mdEntries := ⟨mdEntries_, fits_mdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotDataOfCashAuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotDataOfCashAuctionMessage) : (encode message).length ≤ 68719476781 := by
  have bound_mdEntries := message.mdEntries.length_lt
  have bound_mdEntries_items := encodeMany_length_le MdEntries.encode 34359738392 MdEntries.encode_length_le message.mdEntries.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotDataOfCashAuctionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 4 MdEntries.encode MdEntries.decode MdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdEntries.length_lt]
  rfl

end SnapshotDataOfCashAuctionMessage

/-- Sub Trading Phase Codes: 9 bytes -/
structure SubTradingPhaseCodes where
  subTradingPhaseCode : Alpha 8
  tradingType : BitVec 8
  deriving DecidableEq, Repr

namespace SubTradingPhaseCodes

def encode (message : SubTradingPhaseCodes) : List UInt8 :=
  Alpha.encode message.subTradingPhaseCode
    ++ (encodeUInt 1 message.tradingType)

def decode (bytes : List UInt8) : Option (SubTradingPhaseCodes × List UInt8) := do
  let (subTradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (tradingType, bytes) ← decodeUInt 1 bytes
  pure ({ subTradingPhaseCode, tradingType }, bytes)

@[simp] theorem encode_length (message : SubTradingPhaseCodes) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SubTradingPhaseCodes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubTradingPhaseCodes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SubTradingPhaseCodes

/-- Snapshot Data Of Spot Bond Trading Message -/
structure SnapshotDataOfSpotBondTradingMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  mdEntries : Bounded 4 MdEntries
  subTradingPhaseCodes : Bounded 4 SubTradingPhaseCodes
  auctionVolumeTrade : BitVec 64
  auctionValueTrade : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotDataOfSpotBondTradingMessage

def encode (message : SnapshotDataOfSpotBondTradingMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdEntries.val.length)
    ++ (encodeMany MdEntries.encode message.mdEntries.val
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.subTradingPhaseCodes.val.length)
    ++ (encodeMany SubTradingPhaseCodes.encode message.subTradingPhaseCodes.val
    ++ (encodeUInt 8 message.auctionVolumeTrade
    ++ (encodeUInt 8 message.auctionValueTrade)))))))))))))))

def decode (bytes : List UInt8) : Option (SnapshotDataOfSpotBondTradingMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (mdEntries_, bytes) ← decodeMany MdEntries.decode noMdEntries.toNat bytes
  let (noSubTradingPhaseCodes, bytes) ← decodeUInt 4 bytes
  let (subTradingPhaseCodes_, bytes) ← decodeMany SubTradingPhaseCodes.decode noSubTradingPhaseCodes.toNat bytes
  let (auctionVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (auctionValueTrade, bytes) ← decodeUInt 8 bytes
  if fits_mdEntries : mdEntries_.length < 256 ^ 4 then
    if fits_subTradingPhaseCodes : subTradingPhaseCodes_.length < 256 ^ 4 then
      pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, mdEntries := ⟨mdEntries_, fits_mdEntries⟩, subTradingPhaseCodes := ⟨subTradingPhaseCodes_, fits_subTradingPhaseCodes⟩, auctionVolumeTrade, auctionValueTrade }, bytes)
    else none
  else none

theorem encode_length_pos (message : SnapshotDataOfSpotBondTradingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotDataOfSpotBondTradingMessage) : (encode message).length ≤ 107374182456 := by
  have bound_mdEntries := message.mdEntries.length_lt
  have bound_mdEntries_items := encodeMany_length_le MdEntries.encode 34359738392 MdEntries.encode_length_le message.mdEntries.val
  have bound_subTradingPhaseCodes := message.subTradingPhaseCodes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const SubTradingPhaseCodes.encode 9 SubTradingPhaseCodes.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotDataOfSpotBondTradingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 4 MdEntries.encode MdEntries.decode MdEntries.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 4 SubTradingPhaseCodes.encode SubTradingPhaseCodes.decode SubTradingPhaseCodes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.mdEntries.length_lt, dite_eq_left message.subTradingPhaseCodes.length_lt]
  rfl

end SnapshotDataOfSpotBondTradingMessage

/-- Trade Md Entries: 18 bytes -/
structure TradeMdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMdEntries

def encode (message : TradeMdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx
    ++ (encodeUInt 8 message.mdEntrySize))

def decode (bytes : List UInt8) : Option (TradeMdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  let (mdEntrySize, bytes) ← decodeUInt 8 bytes
  pure ({ mdEntryType, mdEntryPx, mdEntrySize }, bytes)

@[simp] theorem encode_length (message : TradeMdEntries) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeMdEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMdEntries) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMdEntries

/-- Snapshot Data Of After Hour Trading Block Trade Message -/
structure SnapshotDataOfAfterHourTradingBlockTradeMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  tradeMdEntries : Bounded 4 TradeMdEntries
  deriving DecidableEq, Repr

namespace SnapshotDataOfAfterHourTradingBlockTradeMessage

def encode (message : SnapshotDataOfAfterHourTradingBlockTradeMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.tradeMdEntries.val.length)
    ++ (encodeMany TradeMdEntries.encode message.tradeMdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (SnapshotDataOfAfterHourTradingBlockTradeMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (tradeMdEntries_, bytes) ← decodeMany TradeMdEntries.decode noMdEntries.toNat bytes
  if fits_tradeMdEntries : tradeMdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, tradeMdEntries := ⟨tradeMdEntries_, fits_tradeMdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotDataOfAfterHourTradingBlockTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotDataOfAfterHourTradingBlockTradeMessage) : (encode message).length ≤ 77309411379 := by
  have bound_tradeMdEntries := message.tradeMdEntries.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const TradeMdEntries.encode 18 TradeMdEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotDataOfAfterHourTradingBlockTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 4 TradeMdEntries.encode TradeMdEntries.decode TradeMdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeMdEntries.length_lt]
  rfl

end SnapshotDataOfAfterHourTradingBlockTradeMessage

/-- Snapshot Data Of After Hour Trading Message -/
structure SnapshotDataOfAfterHourTradingMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  tradeMdEntries : Bounded 4 TradeMdEntries
  deriving DecidableEq, Repr

namespace SnapshotDataOfAfterHourTradingMessage

def encode (message : SnapshotDataOfAfterHourTradingMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.tradeMdEntries.val.length)
    ++ (encodeMany TradeMdEntries.encode message.tradeMdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (SnapshotDataOfAfterHourTradingMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (tradeMdEntries_, bytes) ← decodeMany TradeMdEntries.decode noMdEntries.toNat bytes
  if fits_tradeMdEntries : tradeMdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, tradeMdEntries := ⟨tradeMdEntries_, fits_tradeMdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotDataOfAfterHourTradingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotDataOfAfterHourTradingMessage) : (encode message).length ≤ 77309411379 := by
  have bound_tradeMdEntries := message.tradeMdEntries.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const TradeMdEntries.encode 18 TradeMdEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotDataOfAfterHourTradingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 4 TradeMdEntries.encode TradeMdEntries.decode TradeMdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeMdEntries.length_lt]
  rfl

end SnapshotDataOfAfterHourTradingMessage

/-- Hk Stocks Md Entries: 20 bytes -/
structure HkStocksMdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdPriceLevel : BitVec 16
  deriving DecidableEq, Repr

namespace HkStocksMdEntries

def encode (message : HkStocksMdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx
    ++ (encodeUInt 8 message.mdEntrySize
    ++ (encodeUInt 2 message.mdPriceLevel)))

def decode (bytes : List UInt8) : Option (HkStocksMdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  let (mdEntrySize, bytes) ← decodeUInt 8 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 2 bytes
  pure ({ mdEntryType, mdEntryPx, mdEntrySize, mdPriceLevel }, bytes)

@[simp] theorem encode_length (message : HkStocksMdEntries) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : HkStocksMdEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HkStocksMdEntries) (rest : List UInt8) :
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

end HkStocksMdEntries

/-- Complex Event Times: 16 bytes -/
structure ComplexEventTimes where
  complexEventStartTime : BitVec 64
  complexEventEndTime : BitVec 64
  deriving DecidableEq, Repr

namespace ComplexEventTimes

def encode (message : ComplexEventTimes) : List UInt8 :=
  encodeUInt 8 message.complexEventStartTime
    ++ (encodeUInt 8 message.complexEventEndTime)

def decode (bytes : List UInt8) : Option (ComplexEventTimes × List UInt8) := do
  let (complexEventStartTime, bytes) ← decodeUInt 8 bytes
  let (complexEventEndTime, bytes) ← decodeUInt 8 bytes
  pure ({ complexEventStartTime, complexEventEndTime }, bytes)

@[simp] theorem encode_length (message : ComplexEventTimes) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ComplexEventTimes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexEventTimes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ComplexEventTimes

/-- Snapshot Data Of Eligible Hk Stocks Message -/
structure SnapshotDataOfEligibleHkStocksMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  hkStocksMdEntries : Bounded 4 HkStocksMdEntries
  complexEventTimes : Bounded 4 ComplexEventTimes
  deriving DecidableEq, Repr

namespace SnapshotDataOfEligibleHkStocksMessage

def encode (message : SnapshotDataOfEligibleHkStocksMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.hkStocksMdEntries.val.length)
    ++ (encodeMany HkStocksMdEntries.encode message.hkStocksMdEntries.val
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.complexEventTimes.val.length)
    ++ (encodeMany ComplexEventTimes.encode message.complexEventTimes.val)))))))))))))

def decode (bytes : List UInt8) : Option (SnapshotDataOfEligibleHkStocksMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (hkStocksMdEntries_, bytes) ← decodeMany HkStocksMdEntries.decode noMdEntries.toNat bytes
  let (noComplexEventTimes, bytes) ← decodeUInt 4 bytes
  let (complexEventTimes_, bytes) ← decodeMany ComplexEventTimes.decode noComplexEventTimes.toNat bytes
  if fits_hkStocksMdEntries : hkStocksMdEntries_.length < 256 ^ 4 then
    if fits_complexEventTimes : complexEventTimes_.length < 256 ^ 4 then
      pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, hkStocksMdEntries := ⟨hkStocksMdEntries_, fits_hkStocksMdEntries⟩, complexEventTimes := ⟨complexEventTimes_, fits_complexEventTimes⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : SnapshotDataOfEligibleHkStocksMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotDataOfEligibleHkStocksMessage) : (encode message).length ≤ 154618822693 := by
  have bound_hkStocksMdEntries := message.hkStocksMdEntries.length_lt
  have bound_complexEventTimes := message.complexEventTimes.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const HkStocksMdEntries.encode 20 HkStocksMdEntries.encode_length, encodeMany_length_const ComplexEventTimes.encode 16 ComplexEventTimes.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotDataOfEligibleHkStocksMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 4 HkStocksMdEntries.encode HkStocksMdEntries.decode HkStocksMdEntries.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 ComplexEventTimes.encode ComplexEventTimes.decode ComplexEventTimes.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.hkStocksMdEntries.length_lt, dite_eq_left message.complexEventTimes.length_lt]
  rfl

end SnapshotDataOfEligibleHkStocksMessage

/-- Index Md Entries: 10 bytes -/
structure IndexMdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMdEntries

def encode (message : IndexMdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx)

def decode (bytes : List UInt8) : Option (IndexMdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  pure ({ mdEntryType, mdEntryPx }, bytes)

@[simp] theorem encode_length (message : IndexMdEntries) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IndexMdEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMdEntries) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMdEntries

/-- Index Snapshot Message -/
structure IndexSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  indexMdEntries : Bounded 4 IndexMdEntries
  deriving DecidableEq, Repr

namespace IndexSnapshotMessage

def encode (message : IndexSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.indexMdEntries.val.length)
    ++ (encodeMany IndexMdEntries.encode message.indexMdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (IndexSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (indexMdEntries_, bytes) ← decodeMany IndexMdEntries.decode noMdEntries.toNat bytes
  if fits_indexMdEntries : indexMdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, indexMdEntries := ⟨indexMdEntries_, fits_indexMdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : IndexSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndexSnapshotMessage) : (encode message).length ≤ 42949673019 := by
  have bound_indexMdEntries := message.indexMdEntries.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const IndexMdEntries.encode 10 IndexMdEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : IndexSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 4 IndexMdEntries.encode IndexMdEntries.decode IndexMdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.indexMdEntries.length_lt]
  rfl

end IndexSnapshotMessage

/-- Statistic Indicator Snapshot Message: 69 bytes -/
structure StatisticIndicatorSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  stockNum : BitVec 32
  deriving DecidableEq, Repr

namespace StatisticIndicatorSnapshotMessage

def encode (message : StatisticIndicatorSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 message.stockNum))))))))))

def decode (bytes : List UInt8) : Option (StatisticIndicatorSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (stockNum, bytes) ← decodeUInt 4 bytes
  pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, stockNum }, bytes)

@[simp] theorem encode_length (message : StatisticIndicatorSnapshotMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticIndicatorSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticIndicatorSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end StatisticIndicatorSnapshotMessage

/-- Real Time Reference Net Value Of Funds Snapshot Message -/
structure RealTimeReferenceNetValueOfFundsSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  prevClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  indexMdEntries : Bounded 4 IndexMdEntries
  deriving DecidableEq, Repr

namespace RealTimeReferenceNetValueOfFundsSnapshotMessage

def encode (message : RealTimeReferenceNetValueOfFundsSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.prevClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.indexMdEntries.val.length)
    ++ (encodeMany IndexMdEntries.encode message.indexMdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (RealTimeReferenceNetValueOfFundsSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (prevClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (indexMdEntries_, bytes) ← decodeMany IndexMdEntries.decode noMdEntries.toNat bytes
  if fits_indexMdEntries : indexMdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, prevClosePx, numTrades, totalVolumeTrade, totalValueTrade, indexMdEntries := ⟨indexMdEntries_, fits_indexMdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : RealTimeReferenceNetValueOfFundsSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RealTimeReferenceNetValueOfFundsSnapshotMessage) : (encode message).length ≤ 42949673019 := by
  have bound_indexMdEntries := message.indexMdEntries.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const IndexMdEntries.encode 10 IndexMdEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : RealTimeReferenceNetValueOfFundsSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 4 IndexMdEntries.encode IndexMdEntries.decode IndexMdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.indexMdEntries.length_lt]
  rfl

end RealTimeReferenceNetValueOfFundsSnapshotMessage

/-- Order Tick Data In Call Auction Message: 51 bytes -/
structure OrderTickDataInCallAuctionMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  ordType : OrdType
  deriving DecidableEq, Repr

namespace OrderTickDataInCallAuctionMessage

def encode (message : OrderTickDataInCallAuctionMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (OrdType.encode message.ordType)))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataInCallAuctionMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, ordType }, bytes)

@[simp] theorem encode_length (message : OrderTickDataInCallAuctionMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : OrderTickDataInCallAuctionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataInCallAuctionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrdType.decode_encode, some_bind]
  rfl

end OrderTickDataInCallAuctionMessage

/-- Order Tick Data Of Negotiable Trade Message: 100 bytes -/
structure OrderTickDataOfNegotiableTradeMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  confirmId : Alpha 8
  contactor : Alpha 12
  contactInfo : Alpha 30
  deriving DecidableEq, Repr

namespace OrderTickDataOfNegotiableTradeMessage

def encode (message : OrderTickDataOfNegotiableTradeMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (Alpha.encode message.confirmId
    ++ (Alpha.encode message.contactor
    ++ (Alpha.encode message.contactInfo)))))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataOfNegotiableTradeMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (confirmId, bytes) ← Alpha.decode 8 bytes
  let (contactor, bytes) ← Alpha.decode 12 bytes
  let (contactInfo, bytes) ← Alpha.decode 30 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, confirmId, contactor, contactInfo }, bytes)

@[simp] theorem encode_length (message : OrderTickDataOfNegotiableTradeMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderTickDataOfNegotiableTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataOfNegotiableTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderTickDataOfNegotiableTradeMessage

/-- Order Tick Data Of Security Lending Message: 53 bytes -/
structure OrderTickDataOfSecurityLendingMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  expirationDays : BitVec 16
  expirationType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderTickDataOfSecurityLendingMessage

def encode (message : OrderTickDataOfSecurityLendingMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType))))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataOfSecurityLendingMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, expirationDays, expirationType }, bytes)

@[simp] theorem encode_length (message : OrderTickDataOfSecurityLendingMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderTickDataOfSecurityLendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataOfSecurityLendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderTickDataOfSecurityLendingMessage

/-- Order Tick Data Of Spot Bond Trading Matching Deal Message: 51 bytes -/
structure OrderTickDataOfSpotBondTradingMatchingDealMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  ordType : OrdType
  deriving DecidableEq, Repr

namespace OrderTickDataOfSpotBondTradingMatchingDealMessage

def encode (message : OrderTickDataOfSpotBondTradingMatchingDealMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (OrdType.encode message.ordType)))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataOfSpotBondTradingMatchingDealMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, ordType }, bytes)

@[simp] theorem encode_length (message : OrderTickDataOfSpotBondTradingMatchingDealMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : OrderTickDataOfSpotBondTradingMatchingDealMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataOfSpotBondTradingMatchingDealMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OrdType.decode_encode, some_bind]
  rfl

end OrderTickDataOfSpotBondTradingMatchingDealMessage

/-- Order Tick Data Of Spot Bond Trading Quotation Message: 377 bytes -/
structure OrderTickDataOfSpotBondTradingQuotationMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  quoteId : Alpha 10
  memberId : Alpha 6
  investorType : Alpha 2
  investorId : Alpha 10
  investorName : Alpha 120
  traderCode : Alpha 8
  settlPeriod : BitVec 8
  settlType : BitVec 16
  memo : Alpha 160
  minQty : BitVec 64
  deriving DecidableEq, Repr

namespace OrderTickDataOfSpotBondTradingQuotationMessage

def encode (message : OrderTickDataOfSpotBondTradingQuotationMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (Alpha.encode message.quoteId
    ++ (Alpha.encode message.memberId
    ++ (Alpha.encode message.investorType
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.investorName
    ++ (Alpha.encode message.traderCode
    ++ (encodeUInt 1 message.settlPeriod
    ++ (encodeUInt 2 message.settlType
    ++ (Alpha.encode message.memo
    ++ (encodeUInt 8 message.minQty))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataOfSpotBondTradingQuotationMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (quoteId, bytes) ← Alpha.decode 10 bytes
  let (memberId, bytes) ← Alpha.decode 6 bytes
  let (investorType, bytes) ← Alpha.decode 2 bytes
  let (investorId, bytes) ← Alpha.decode 10 bytes
  let (investorName, bytes) ← Alpha.decode 120 bytes
  let (traderCode, bytes) ← Alpha.decode 8 bytes
  let (settlPeriod, bytes) ← decodeUInt 1 bytes
  let (settlType, bytes) ← decodeUInt 2 bytes
  let (memo, bytes) ← Alpha.decode 160 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, quoteId, memberId, investorType, investorId, investorName, traderCode, settlPeriod, settlType, memo, minQty }, bytes)

@[simp] theorem encode_length (message : OrderTickDataOfSpotBondTradingQuotationMessage) : (encode message).length = 377 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderTickDataOfSpotBondTradingQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataOfSpotBondTradingQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderTickDataOfSpotBondTradingQuotationMessage

/-- Order Tick Data Of Bid Quotation Message: 407 bytes -/
structure OrderTickDataOfBidQuotationMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transacTime : BitVec 64
  memberId : Alpha 6
  investorType : Alpha 2
  investorId : Alpha 10
  investorName : Alpha 120
  traderCode : Alpha 8
  settlPeriod : BitVec 8
  settlType : BitVec 16
  memo : Alpha 160
  secondaryOrderId : Alpha 16
  bidTransType : BitVec 16
  bidExecInstType : BitVec 16
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  minQty : BitVec 64
  tradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace OrderTickDataOfBidQuotationMessage

def encode (message : OrderTickDataOfBidQuotationMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transacTime
    ++ (Alpha.encode message.memberId
    ++ (Alpha.encode message.investorType
    ++ (Alpha.encode message.investorId
    ++ (Alpha.encode message.investorName
    ++ (Alpha.encode message.traderCode
    ++ (encodeUInt 1 message.settlPeriod
    ++ (encodeUInt 2 message.settlType
    ++ (Alpha.encode message.memo
    ++ (Alpha.encode message.secondaryOrderId
    ++ (encodeUInt 2 message.bidTransType
    ++ (encodeUInt 2 message.bidExecInstType
    ++ (encodeUInt 8 message.lowLimitPrice
    ++ (encodeUInt 8 message.highLimitPrice
    ++ (encodeUInt 8 message.minQty
    ++ (encodeUInt 4 message.tradeDate)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderTickDataOfBidQuotationMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (memberId, bytes) ← Alpha.decode 6 bytes
  let (investorType, bytes) ← Alpha.decode 2 bytes
  let (investorId, bytes) ← Alpha.decode 10 bytes
  let (investorName, bytes) ← Alpha.decode 120 bytes
  let (traderCode, bytes) ← Alpha.decode 8 bytes
  let (settlPeriod, bytes) ← decodeUInt 1 bytes
  let (settlType, bytes) ← decodeUInt 2 bytes
  let (memo, bytes) ← Alpha.decode 160 bytes
  let (secondaryOrderId, bytes) ← Alpha.decode 16 bytes
  let (bidTransType, bytes) ← decodeUInt 2 bytes
  let (bidExecInstType, bytes) ← decodeUInt 2 bytes
  let (lowLimitPrice, bytes) ← decodeUInt 8 bytes
  let (highLimitPrice, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  let (tradeDate, bytes) ← decodeUInt 4 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transacTime, memberId, investorType, investorId, investorName, traderCode, settlPeriod, settlType, memo, secondaryOrderId, bidTransType, bidExecInstType, lowLimitPrice, highLimitPrice, minQty, tradeDate }, bytes)

@[simp] theorem encode_length (message : OrderTickDataOfBidQuotationMessage) : (encode message).length = 407 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderTickDataOfBidQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderTickDataOfBidQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderTickDataOfBidQuotationMessage

/-- Transaction Tick Data In Call Auction Message: 66 bytes -/
structure TransactionTickDataInCallAuctionMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  deriving DecidableEq, Repr

namespace TransactionTickDataInCallAuctionMessage

def encode (message : TransactionTickDataInCallAuctionMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataInCallAuctionMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataInCallAuctionMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataInCallAuctionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataInCallAuctionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataInCallAuctionMessage

/-- Transaction Tick Data Of Negotiable Trade Message: 66 bytes -/
structure TransactionTickDataOfNegotiableTradeMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  deriving DecidableEq, Repr

namespace TransactionTickDataOfNegotiableTradeMessage

def encode (message : TransactionTickDataOfNegotiableTradeMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataOfNegotiableTradeMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataOfNegotiableTradeMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataOfNegotiableTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataOfNegotiableTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataOfNegotiableTradeMessage

/-- Transaction Tick Data Of Security Lending Message: 66 bytes -/
structure TransactionTickDataOfSecurityLendingMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  deriving DecidableEq, Repr

namespace TransactionTickDataOfSecurityLendingMessage

def encode (message : TransactionTickDataOfSecurityLendingMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataOfSecurityLendingMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataOfSecurityLendingMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataOfSecurityLendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataOfSecurityLendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataOfSecurityLendingMessage

/-- Transaction Tick Data Of Bond General Pledged Repo Message: 66 bytes -/
structure TransactionTickDataOfBondGeneralPledgedRepoMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  deriving DecidableEq, Repr

namespace TransactionTickDataOfBondGeneralPledgedRepoMessage

def encode (message : TransactionTickDataOfBondGeneralPledgedRepoMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataOfBondGeneralPledgedRepoMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataOfBondGeneralPledgedRepoMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataOfBondGeneralPledgedRepoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataOfBondGeneralPledgedRepoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataOfBondGeneralPledgedRepoMessage

/-- Transaction Tick Data Of Spot Bond Trading Quotation Message: 69 bytes -/
structure TransactionTickDataOfSpotBondTradingQuotationMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  settlPeriod : BitVec 8
  settlType : BitVec 16
  deriving DecidableEq, Repr

namespace TransactionTickDataOfSpotBondTradingQuotationMessage

def encode (message : TransactionTickDataOfSpotBondTradingQuotationMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime
    ++ (encodeUInt 1 message.settlPeriod
    ++ (encodeUInt 2 message.settlType))))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataOfSpotBondTradingQuotationMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (settlPeriod, bytes) ← decodeUInt 1 bytes
  let (settlType, bytes) ← decodeUInt 2 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime, settlPeriod, settlType }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataOfSpotBondTradingQuotationMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataOfSpotBondTradingQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataOfSpotBondTradingQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataOfSpotBondTradingQuotationMessage

/-- Transaction Tick Data Of Bid Quotation Message: 95 bytes -/
structure TransactionTickDataOfBidQuotationMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  bidApplSeqNum : BitVec 64
  offerApplSeqNum : BitVec 64
  securityId : Alpha 8
  securityIdSource : Alpha 4
  lastPx : BitVec 64
  lastQty : BitVec 64
  execType : ExecType
  transacTime : BitVec 64
  settlPeriod : BitVec 8
  settlType : BitVec 16
  secondaryOrderId : Alpha 16
  bidExecInstType : BitVec 16
  marginPrice : BitVec 64
  deriving DecidableEq, Repr

namespace TransactionTickDataOfBidQuotationMessage

def encode (message : TransactionTickDataOfBidQuotationMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.offerApplSeqNum
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transacTime
    ++ (encodeUInt 1 message.settlPeriod
    ++ (encodeUInt 2 message.settlType
    ++ (Alpha.encode message.secondaryOrderId
    ++ (encodeUInt 2 message.bidExecInstType
    ++ (encodeUInt 8 message.marginPrice)))))))))))))))

def decode (bytes : List UInt8) : Option (TransactionTickDataOfBidQuotationMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (offerApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transacTime, bytes) ← decodeUInt 8 bytes
  let (settlPeriod, bytes) ← decodeUInt 1 bytes
  let (settlType, bytes) ← decodeUInt 2 bytes
  let (secondaryOrderId, bytes) ← Alpha.decode 16 bytes
  let (bidExecInstType, bytes) ← decodeUInt 2 bytes
  let (marginPrice, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, bidApplSeqNum, offerApplSeqNum, securityId, securityIdSource, lastPx, lastQty, execType, transacTime, settlPeriod, settlType, secondaryOrderId, bidExecInstType, marginPrice }, bytes)

@[simp] theorem encode_length (message : TransactionTickDataOfBidQuotationMessage) : (encode message).length = 95 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : TransactionTickDataOfBidQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactionTickDataOfBidQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactionTickDataOfBidQuotationMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 1
  | logoutMessage (message : LogoutMessage) -- 2
  | channelHeartbeatMessage (message : ChannelHeartbeatMessage) -- 390095
  | retransmittingMessage (message : RetransmittingMessage) -- 390094
  | clientUserInformationReportingMessage (message : ClientUserInformationReportingMessage) -- 390093
  | statisticsOfSnapshotDataChannelMessage (message : StatisticsOfSnapshotDataChannelMessage) -- 390090
  | businessRejectMessage (message : BusinessRejectMessage) -- 8
  | realTimeMarketStatusMessage (message : RealTimeMarketStatusMessage) -- 390019
  | realTimeStatusOfSecurityMessage (message : RealTimeStatusOfSecurityMessage) -- 390013
  | announcementsMessage (message : AnnouncementsMessage) -- 390012
  | snapshotDataOfCashAuctionMessage (message : SnapshotDataOfCashAuctionMessage) -- 300111
  | snapshotDataOfSpotBondTradingMessage (message : SnapshotDataOfSpotBondTradingMessage) -- 300211
  | snapshotDataOfAfterHourTradingBlockTradeMessage (message : SnapshotDataOfAfterHourTradingBlockTradeMessage) -- 300611
  | snapshotDataOfAfterHourTradingMessage (message : SnapshotDataOfAfterHourTradingMessage) -- 303711
  | snapshotDataOfEligibleHkStocksMessage (message : SnapshotDataOfEligibleHkStocksMessage) -- 306311
  | indexSnapshotMessage (message : IndexSnapshotMessage) -- 309011
  | statisticIndicatorSnapshotMessage (message : StatisticIndicatorSnapshotMessage) -- 309111
  | realTimeReferenceNetValueOfFundsSnapshotMessage (message : RealTimeReferenceNetValueOfFundsSnapshotMessage) -- 309211
  | orderTickDataInCallAuctionMessage (message : OrderTickDataInCallAuctionMessage) -- 300192
  | orderTickDataOfNegotiableTradeMessage (message : OrderTickDataOfNegotiableTradeMessage) -- 300592
  | orderTickDataOfSecurityLendingMessage (message : OrderTickDataOfSecurityLendingMessage) -- 300792
  | orderTickDataOfSpotBondTradingMatchingDealMessage (message : OrderTickDataOfSpotBondTradingMatchingDealMessage) -- 300292
  | orderTickDataOfSpotBondTradingQuotationMessage (message : OrderTickDataOfSpotBondTradingQuotationMessage) -- 300392
  | orderTickDataOfBidQuotationMessage (message : OrderTickDataOfBidQuotationMessage) -- 300492
  | transactionTickDataInCallAuctionMessage (message : TransactionTickDataInCallAuctionMessage) -- 300191
  | transactionTickDataOfNegotiableTradeMessage (message : TransactionTickDataOfNegotiableTradeMessage) -- 300591
  | transactionTickDataOfSecurityLendingMessage (message : TransactionTickDataOfSecurityLendingMessage) -- 300791
  | transactionTickDataOfBondGeneralPledgedRepoMessage (message : TransactionTickDataOfBondGeneralPledgedRepoMessage) -- 300291
  | transactionTickDataOfSpotBondTradingQuotationMessage (message : TransactionTickDataOfSpotBondTradingQuotationMessage) -- 300391
  | transactionTickDataOfBidQuotationMessage (message : TransactionTickDataOfBidQuotationMessage) -- 300491
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 32
  | .logonMessage _ => 1
  | .logoutMessage _ => 2
  | .channelHeartbeatMessage _ => 390095
  | .retransmittingMessage _ => 390094
  | .clientUserInformationReportingMessage _ => 390093
  | .statisticsOfSnapshotDataChannelMessage _ => 390090
  | .businessRejectMessage _ => 8
  | .realTimeMarketStatusMessage _ => 390019
  | .realTimeStatusOfSecurityMessage _ => 390013
  | .announcementsMessage _ => 390012
  | .snapshotDataOfCashAuctionMessage _ => 300111
  | .snapshotDataOfSpotBondTradingMessage _ => 300211
  | .snapshotDataOfAfterHourTradingBlockTradeMessage _ => 300611
  | .snapshotDataOfAfterHourTradingMessage _ => 303711
  | .snapshotDataOfEligibleHkStocksMessage _ => 306311
  | .indexSnapshotMessage _ => 309011
  | .statisticIndicatorSnapshotMessage _ => 309111
  | .realTimeReferenceNetValueOfFundsSnapshotMessage _ => 309211
  | .orderTickDataInCallAuctionMessage _ => 300192
  | .orderTickDataOfNegotiableTradeMessage _ => 300592
  | .orderTickDataOfSecurityLendingMessage _ => 300792
  | .orderTickDataOfSpotBondTradingMatchingDealMessage _ => 300292
  | .orderTickDataOfSpotBondTradingQuotationMessage _ => 300392
  | .orderTickDataOfBidQuotationMessage _ => 300492
  | .transactionTickDataInCallAuctionMessage _ => 300191
  | .transactionTickDataOfNegotiableTradeMessage _ => 300591
  | .transactionTickDataOfSecurityLendingMessage _ => 300791
  | .transactionTickDataOfBondGeneralPledgedRepoMessage _ => 300291
  | .transactionTickDataOfSpotBondTradingQuotationMessage _ => 300391
  | .transactionTickDataOfBidQuotationMessage _ => 300491

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .channelHeartbeatMessage message => ChannelHeartbeatMessage.encode message
  | .retransmittingMessage message => RetransmittingMessage.encode message
  | .clientUserInformationReportingMessage message => ClientUserInformationReportingMessage.encode message
  | .statisticsOfSnapshotDataChannelMessage message => StatisticsOfSnapshotDataChannelMessage.encode message
  | .businessRejectMessage message => BusinessRejectMessage.encode message
  | .realTimeMarketStatusMessage message => RealTimeMarketStatusMessage.encode message
  | .realTimeStatusOfSecurityMessage message => RealTimeStatusOfSecurityMessage.encode message
  | .announcementsMessage message => AnnouncementsMessage.encode message
  | .snapshotDataOfCashAuctionMessage message => SnapshotDataOfCashAuctionMessage.encode message
  | .snapshotDataOfSpotBondTradingMessage message => SnapshotDataOfSpotBondTradingMessage.encode message
  | .snapshotDataOfAfterHourTradingBlockTradeMessage message => SnapshotDataOfAfterHourTradingBlockTradeMessage.encode message
  | .snapshotDataOfAfterHourTradingMessage message => SnapshotDataOfAfterHourTradingMessage.encode message
  | .snapshotDataOfEligibleHkStocksMessage message => SnapshotDataOfEligibleHkStocksMessage.encode message
  | .indexSnapshotMessage message => IndexSnapshotMessage.encode message
  | .statisticIndicatorSnapshotMessage message => StatisticIndicatorSnapshotMessage.encode message
  | .realTimeReferenceNetValueOfFundsSnapshotMessage message => RealTimeReferenceNetValueOfFundsSnapshotMessage.encode message
  | .orderTickDataInCallAuctionMessage message => OrderTickDataInCallAuctionMessage.encode message
  | .orderTickDataOfNegotiableTradeMessage message => OrderTickDataOfNegotiableTradeMessage.encode message
  | .orderTickDataOfSecurityLendingMessage message => OrderTickDataOfSecurityLendingMessage.encode message
  | .orderTickDataOfSpotBondTradingMatchingDealMessage message => OrderTickDataOfSpotBondTradingMatchingDealMessage.encode message
  | .orderTickDataOfSpotBondTradingQuotationMessage message => OrderTickDataOfSpotBondTradingQuotationMessage.encode message
  | .orderTickDataOfBidQuotationMessage message => OrderTickDataOfBidQuotationMessage.encode message
  | .transactionTickDataInCallAuctionMessage message => TransactionTickDataInCallAuctionMessage.encode message
  | .transactionTickDataOfNegotiableTradeMessage message => TransactionTickDataOfNegotiableTradeMessage.encode message
  | .transactionTickDataOfSecurityLendingMessage message => TransactionTickDataOfSecurityLendingMessage.encode message
  | .transactionTickDataOfBondGeneralPledgedRepoMessage message => TransactionTickDataOfBondGeneralPledgedRepoMessage.encode message
  | .transactionTickDataOfSpotBondTradingQuotationMessage message => TransactionTickDataOfSpotBondTradingQuotationMessage.encode message
  | .transactionTickDataOfBidQuotationMessage message => TransactionTickDataOfBidQuotationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 154618822693 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | channelHeartbeatMessage inner =>
    simp only [encode, ChannelHeartbeatMessage.encode_length]
    omega
  | retransmittingMessage inner =>
    simp only [encode, RetransmittingMessage.encode_length]
    omega
  | clientUserInformationReportingMessage inner =>
    simp only [encode, ClientUserInformationReportingMessage.encode_length]
    omega
  | statisticsOfSnapshotDataChannelMessage inner =>
    have bound_inner := StatisticsOfSnapshotDataChannelMessage.encode_length_le inner
    simp only [encode]
    omega
  | businessRejectMessage inner =>
    simp only [encode, BusinessRejectMessage.encode_length]
    omega
  | realTimeMarketStatusMessage inner =>
    simp only [encode, RealTimeMarketStatusMessage.encode_length]
    omega
  | realTimeStatusOfSecurityMessage inner =>
    have bound_inner := RealTimeStatusOfSecurityMessage.encode_length_le inner
    simp only [encode]
    omega
  | announcementsMessage inner =>
    have bound_inner := AnnouncementsMessage.encode_length_le inner
    simp only [encode]
    omega
  | snapshotDataOfCashAuctionMessage inner =>
    have bound_inner := SnapshotDataOfCashAuctionMessage.encode_length_le inner
    simp only [encode]
    omega
  | snapshotDataOfSpotBondTradingMessage inner =>
    have bound_inner := SnapshotDataOfSpotBondTradingMessage.encode_length_le inner
    simp only [encode]
    omega
  | snapshotDataOfAfterHourTradingBlockTradeMessage inner =>
    have bound_inner := SnapshotDataOfAfterHourTradingBlockTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | snapshotDataOfAfterHourTradingMessage inner =>
    have bound_inner := SnapshotDataOfAfterHourTradingMessage.encode_length_le inner
    simp only [encode]
    omega
  | snapshotDataOfEligibleHkStocksMessage inner =>
    have bound_inner := SnapshotDataOfEligibleHkStocksMessage.encode_length_le inner
    simp only [encode]
    omega
  | indexSnapshotMessage inner =>
    have bound_inner := IndexSnapshotMessage.encode_length_le inner
    simp only [encode]
    omega
  | statisticIndicatorSnapshotMessage inner =>
    simp only [encode, StatisticIndicatorSnapshotMessage.encode_length]
    omega
  | realTimeReferenceNetValueOfFundsSnapshotMessage inner =>
    have bound_inner := RealTimeReferenceNetValueOfFundsSnapshotMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderTickDataInCallAuctionMessage inner =>
    simp only [encode, OrderTickDataInCallAuctionMessage.encode_length]
    omega
  | orderTickDataOfNegotiableTradeMessage inner =>
    simp only [encode, OrderTickDataOfNegotiableTradeMessage.encode_length]
    omega
  | orderTickDataOfSecurityLendingMessage inner =>
    simp only [encode, OrderTickDataOfSecurityLendingMessage.encode_length]
    omega
  | orderTickDataOfSpotBondTradingMatchingDealMessage inner =>
    simp only [encode, OrderTickDataOfSpotBondTradingMatchingDealMessage.encode_length]
    omega
  | orderTickDataOfSpotBondTradingQuotationMessage inner =>
    simp only [encode, OrderTickDataOfSpotBondTradingQuotationMessage.encode_length]
    omega
  | orderTickDataOfBidQuotationMessage inner =>
    simp only [encode, OrderTickDataOfBidQuotationMessage.encode_length]
    omega
  | transactionTickDataInCallAuctionMessage inner =>
    simp only [encode, TransactionTickDataInCallAuctionMessage.encode_length]
    omega
  | transactionTickDataOfNegotiableTradeMessage inner =>
    simp only [encode, TransactionTickDataOfNegotiableTradeMessage.encode_length]
    omega
  | transactionTickDataOfSecurityLendingMessage inner =>
    simp only [encode, TransactionTickDataOfSecurityLendingMessage.encode_length]
    omega
  | transactionTickDataOfBondGeneralPledgedRepoMessage inner =>
    simp only [encode, TransactionTickDataOfBondGeneralPledgedRepoMessage.encode_length]
    omega
  | transactionTickDataOfSpotBondTradingQuotationMessage inner =>
    simp only [encode, TransactionTickDataOfSpotBondTradingQuotationMessage.encode_length]
    omega
  | transactionTickDataOfBidQuotationMessage inner =>
    simp only [encode, TransactionTickDataOfBidQuotationMessage.encode_length]
    omega

def decode (tag : BitVec 32) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 2 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 390095 then (ChannelHeartbeatMessage.decode bytes).map fun (message, rest) => (.channelHeartbeatMessage message, rest)
  else if tag = 390094 then (RetransmittingMessage.decode bytes).map fun (message, rest) => (.retransmittingMessage message, rest)
  else if tag = 390093 then (ClientUserInformationReportingMessage.decode bytes).map fun (message, rest) => (.clientUserInformationReportingMessage message, rest)
  else if tag = 390090 then (StatisticsOfSnapshotDataChannelMessage.decode bytes).map fun (message, rest) => (.statisticsOfSnapshotDataChannelMessage message, rest)
  else if tag = 8 then (BusinessRejectMessage.decode bytes).map fun (message, rest) => (.businessRejectMessage message, rest)
  else if tag = 390019 then (RealTimeMarketStatusMessage.decode bytes).map fun (message, rest) => (.realTimeMarketStatusMessage message, rest)
  else if tag = 390013 then (RealTimeStatusOfSecurityMessage.decode bytes).map fun (message, rest) => (.realTimeStatusOfSecurityMessage message, rest)
  else if tag = 390012 then (AnnouncementsMessage.decode bytes).map fun (message, rest) => (.announcementsMessage message, rest)
  else if tag = 300111 then (SnapshotDataOfCashAuctionMessage.decode bytes).map fun (message, rest) => (.snapshotDataOfCashAuctionMessage message, rest)
  else if tag = 300211 then (SnapshotDataOfSpotBondTradingMessage.decode bytes).map fun (message, rest) => (.snapshotDataOfSpotBondTradingMessage message, rest)
  else if tag = 300611 then (SnapshotDataOfAfterHourTradingBlockTradeMessage.decode bytes).map fun (message, rest) => (.snapshotDataOfAfterHourTradingBlockTradeMessage message, rest)
  else if tag = 303711 then (SnapshotDataOfAfterHourTradingMessage.decode bytes).map fun (message, rest) => (.snapshotDataOfAfterHourTradingMessage message, rest)
  else if tag = 306311 then (SnapshotDataOfEligibleHkStocksMessage.decode bytes).map fun (message, rest) => (.snapshotDataOfEligibleHkStocksMessage message, rest)
  else if tag = 309011 then (IndexSnapshotMessage.decode bytes).map fun (message, rest) => (.indexSnapshotMessage message, rest)
  else if tag = 309111 then (StatisticIndicatorSnapshotMessage.decode bytes).map fun (message, rest) => (.statisticIndicatorSnapshotMessage message, rest)
  else if tag = 309211 then (RealTimeReferenceNetValueOfFundsSnapshotMessage.decode bytes).map fun (message, rest) => (.realTimeReferenceNetValueOfFundsSnapshotMessage message, rest)
  else if tag = 300192 then (OrderTickDataInCallAuctionMessage.decode bytes).map fun (message, rest) => (.orderTickDataInCallAuctionMessage message, rest)
  else if tag = 300592 then (OrderTickDataOfNegotiableTradeMessage.decode bytes).map fun (message, rest) => (.orderTickDataOfNegotiableTradeMessage message, rest)
  else if tag = 300792 then (OrderTickDataOfSecurityLendingMessage.decode bytes).map fun (message, rest) => (.orderTickDataOfSecurityLendingMessage message, rest)
  else if tag = 300292 then (OrderTickDataOfSpotBondTradingMatchingDealMessage.decode bytes).map fun (message, rest) => (.orderTickDataOfSpotBondTradingMatchingDealMessage message, rest)
  else if tag = 300392 then (OrderTickDataOfSpotBondTradingQuotationMessage.decode bytes).map fun (message, rest) => (.orderTickDataOfSpotBondTradingQuotationMessage message, rest)
  else if tag = 300492 then (OrderTickDataOfBidQuotationMessage.decode bytes).map fun (message, rest) => (.orderTickDataOfBidQuotationMessage message, rest)
  else if tag = 300191 then (TransactionTickDataInCallAuctionMessage.decode bytes).map fun (message, rest) => (.transactionTickDataInCallAuctionMessage message, rest)
  else if tag = 300591 then (TransactionTickDataOfNegotiableTradeMessage.decode bytes).map fun (message, rest) => (.transactionTickDataOfNegotiableTradeMessage message, rest)
  else if tag = 300791 then (TransactionTickDataOfSecurityLendingMessage.decode bytes).map fun (message, rest) => (.transactionTickDataOfSecurityLendingMessage message, rest)
  else if tag = 300291 then (TransactionTickDataOfBondGeneralPledgedRepoMessage.decode bytes).map fun (message, rest) => (.transactionTickDataOfBondGeneralPledgedRepoMessage message, rest)
  else if tag = 300391 then (TransactionTickDataOfSpotBondTradingQuotationMessage.decode bytes).map fun (message, rest) => (.transactionTickDataOfSpotBondTradingQuotationMessage message, rest)
  else if tag = 300491 then (TransactionTickDataOfBidQuotationMessage.decode bytes).map fun (message, rest) => (.transactionTickDataOfBidQuotationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Tail: 4 bytes -/
structure MessageTail where
  checksum : BitVec 32
  deriving DecidableEq, Repr

namespace MessageTail

def encode (message : MessageTail) : List UInt8 :=
  encodeUInt 4 message.checksum

def decode (bytes : List UInt8) : Option (MessageTail × List UInt8) := do
  let (checksum, bytes) ← decodeUInt 4 bytes
  pure ({ checksum }, bytes)

@[simp] theorem encode_length (message : MessageTail) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MessageTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageTail

/-- Message -/
structure Message where
  bodyLength : BitVec 32
  payload : Payload
  messageTail : MessageTail
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 4 (Payload.tag message.payload)
    ++ (encodeUInt 4 message.bodyLength
    ++ (Payload.encode message.payload
    ++ (MessageTail.encode message.messageTail)))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 4 bytes
  let (bodyLength, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  let (messageTail, bytes) ← MessageTail.decode bytes
  pure ({ bodyLength, payload, messageTail }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 154618822705 := by
  unfold encode
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, LogoutMessage.encode_length]
    omega
  | channelHeartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, ChannelHeartbeatMessage.encode_length]
    omega
  | retransmittingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RetransmittingMessage.encode_length]
    omega
  | clientUserInformationReportingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, ClientUserInformationReportingMessage.encode_length]
    omega
  | statisticsOfSnapshotDataChannelMessage inner =>
    have bound_inner := StatisticsOfSnapshotDataChannelMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BusinessRejectMessage.encode_length]
    omega
  | realTimeMarketStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RealTimeMarketStatusMessage.encode_length]
    omega
  | realTimeStatusOfSecurityMessage inner =>
    have bound_inner := RealTimeStatusOfSecurityMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | announcementsMessage inner =>
    have bound_inner := AnnouncementsMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | snapshotDataOfCashAuctionMessage inner =>
    have bound_inner := SnapshotDataOfCashAuctionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | snapshotDataOfSpotBondTradingMessage inner =>
    have bound_inner := SnapshotDataOfSpotBondTradingMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | snapshotDataOfAfterHourTradingBlockTradeMessage inner =>
    have bound_inner := SnapshotDataOfAfterHourTradingBlockTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | snapshotDataOfAfterHourTradingMessage inner =>
    have bound_inner := SnapshotDataOfAfterHourTradingMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | snapshotDataOfEligibleHkStocksMessage inner =>
    have bound_inner := SnapshotDataOfEligibleHkStocksMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | indexSnapshotMessage inner =>
    have bound_inner := IndexSnapshotMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | statisticIndicatorSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, StatisticIndicatorSnapshotMessage.encode_length]
    omega
  | realTimeReferenceNetValueOfFundsSnapshotMessage inner =>
    have bound_inner := RealTimeReferenceNetValueOfFundsSnapshotMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | orderTickDataInCallAuctionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataInCallAuctionMessage.encode_length]
    omega
  | orderTickDataOfNegotiableTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataOfNegotiableTradeMessage.encode_length]
    omega
  | orderTickDataOfSecurityLendingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataOfSecurityLendingMessage.encode_length]
    omega
  | orderTickDataOfSpotBondTradingMatchingDealMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataOfSpotBondTradingMatchingDealMessage.encode_length]
    omega
  | orderTickDataOfSpotBondTradingQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataOfSpotBondTradingQuotationMessage.encode_length]
    omega
  | orderTickDataOfBidQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderTickDataOfBidQuotationMessage.encode_length]
    omega
  | transactionTickDataInCallAuctionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataInCallAuctionMessage.encode_length]
    omega
  | transactionTickDataOfNegotiableTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataOfNegotiableTradeMessage.encode_length]
    omega
  | transactionTickDataOfSecurityLendingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataOfSecurityLendingMessage.encode_length]
    omega
  | transactionTickDataOfBondGeneralPledgedRepoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataOfBondGeneralPledgedRepoMessage.encode_length]
    omega
  | transactionTickDataOfSpotBondTradingQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataOfSpotBondTradingQuotationMessage.encode_length]
    omega
  | transactionTickDataOfBidQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TransactionTickDataOfBidQuotationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [MessageTail.decode_encode, some_bind]
  rfl

end Message

end Omi.SzseSzsesecuritiesTcpmarketdataSzsebinaryV117
