import Wire

/-!
# Nextrade Nextrade Etp Market Data Common v2.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Etp Constituents Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Mm Lp Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Equities Batch Data Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Member Information Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Note: Issue Event Message is selected by more than one code: each is a constructor of its own over the one record, so the code read is the code written back.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NextradeNextradeEtpcommonNxtbinaryV212

/-- Polling Data Message: 8 bytes -/
structure PollingDataMessage where
  currentTime1MinuteInterval : Alpha 4
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace PollingDataMessage

def encode (message : PollingDataMessage) : List UInt8 :=
  Alpha.encode message.currentTime1MinuteInterval
    ++ (encodeUIntLE 4 message.endKeyword)

def decode (bytes : List UInt8) : Option (PollingDataMessage × List UInt8) := do
  let (currentTime1MinuteInterval, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ currentTime1MinuteInterval, endKeyword }, bytes)

@[simp] theorem encode_length (message : PollingDataMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PollingDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PollingDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PollingDataMessage

/-- Securities Quote Mm Lp Quotes Included 10 Level Message: 576 bytes -/
structure SecuritiesQuoteMmLpQuotesIncluded10LevelMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  askLevel1Price : Alpha 8
  bidLevel1Price : Alpha 8
  askLevel1Volume : BitVec 64
  bidLevel1Volume : BitVec 64
  lpAskLevel1Volume : BitVec 64
  lpBidLevel1Volume : BitVec 64
  askLevel2Price : Alpha 8
  bidLevel2Price : Alpha 8
  askLevel2Volume : BitVec 64
  bidLevel2Volume : BitVec 64
  lpAskLevel2Volume : BitVec 64
  lpBidLevel2Volume : BitVec 64
  askLevel3Price : Alpha 8
  bidLevel3Price : Alpha 8
  askLevel3Volume : BitVec 64
  bidLevel3Volume : BitVec 64
  lpAskLevel3Volume : BitVec 64
  lpBidLevel3Volume : BitVec 64
  askLevel4Price : Alpha 8
  bidLevel4Price : Alpha 8
  askLevel4Volume : BitVec 64
  bidLevel4Volume : BitVec 64
  lpAskLevel4Volume : BitVec 64
  lpBidLevel4Volume : BitVec 64
  askLevel5Price : Alpha 8
  bidLevel5Price : Alpha 8
  askLevel5Volume : BitVec 64
  bidLevel5Volume : BitVec 64
  lpAskLevel5Volume : BitVec 64
  lpBidLevel5Volume : BitVec 64
  askLevel6Price : Alpha 8
  bidLevel6Price : Alpha 8
  askLevel6Volume : BitVec 64
  bidLevel6Volume : BitVec 64
  lpAskLevel6Volume : BitVec 64
  lpBidLevel6Volume : BitVec 64
  askLevel7Price : Alpha 8
  bidLevel7Price : Alpha 8
  askLevel7Volume : BitVec 64
  bidLevel7Volume : BitVec 64
  lpAskLevel7Volume : BitVec 64
  lpBidLevel7Volume : BitVec 64
  askLevel8Price : Alpha 8
  bidLevel8Price : Alpha 8
  askLevel8Volume : BitVec 64
  bidLevel8Volume : BitVec 64
  lpAskLevel8Volume : BitVec 64
  lpBidLevel8Volume : BitVec 64
  askLevel9Price : Alpha 8
  bidLevel9Price : Alpha 8
  askLevel9Volume : BitVec 64
  bidLevel9Volume : BitVec 64
  lpAskLevel9Volume : BitVec 64
  lpBidLevel9Volume : BitVec 64
  askLevel10Price : Alpha 8
  bidLevel10Price : Alpha 8
  askLevel10Volume : BitVec 64
  bidLevel10Volume : BitVec 64
  lpAskLevel10Volume : BitVec 64
  lpBidLevel10Volume : BitVec 64
  totalAskVolume : BitVec 64
  totalBidVolume : BitVec 64
  estimatedTradingPrice : Alpha 8
  estimatedTradingVolume : BitVec 64
  midPrice : Alpha 8
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : BitVec 64
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : BitVec 64
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

def encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (encodeUIntLE 8 message.askLevel1Volume
    ++ (encodeUIntLE 8 message.bidLevel1Volume
    ++ (encodeUIntLE 8 message.lpAskLevel1Volume
    ++ (encodeUIntLE 8 message.lpBidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (encodeUIntLE 8 message.askLevel2Volume
    ++ (encodeUIntLE 8 message.bidLevel2Volume
    ++ (encodeUIntLE 8 message.lpAskLevel2Volume
    ++ (encodeUIntLE 8 message.lpBidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (encodeUIntLE 8 message.askLevel3Volume
    ++ (encodeUIntLE 8 message.bidLevel3Volume
    ++ (encodeUIntLE 8 message.lpAskLevel3Volume
    ++ (encodeUIntLE 8 message.lpBidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (encodeUIntLE 8 message.askLevel4Volume
    ++ (encodeUIntLE 8 message.bidLevel4Volume
    ++ (encodeUIntLE 8 message.lpAskLevel4Volume
    ++ (encodeUIntLE 8 message.lpBidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (encodeUIntLE 8 message.askLevel5Volume
    ++ (encodeUIntLE 8 message.bidLevel5Volume
    ++ (encodeUIntLE 8 message.lpAskLevel5Volume
    ++ (encodeUIntLE 8 message.lpBidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (encodeUIntLE 8 message.askLevel6Volume
    ++ (encodeUIntLE 8 message.bidLevel6Volume
    ++ (encodeUIntLE 8 message.lpAskLevel6Volume
    ++ (encodeUIntLE 8 message.lpBidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (encodeUIntLE 8 message.askLevel7Volume
    ++ (encodeUIntLE 8 message.bidLevel7Volume
    ++ (encodeUIntLE 8 message.lpAskLevel7Volume
    ++ (encodeUIntLE 8 message.lpBidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (encodeUIntLE 8 message.askLevel8Volume
    ++ (encodeUIntLE 8 message.bidLevel8Volume
    ++ (encodeUIntLE 8 message.lpAskLevel8Volume
    ++ (encodeUIntLE 8 message.lpBidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (encodeUIntLE 8 message.askLevel9Volume
    ++ (encodeUIntLE 8 message.bidLevel9Volume
    ++ (encodeUIntLE 8 message.lpAskLevel9Volume
    ++ (encodeUIntLE 8 message.lpBidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (encodeUIntLE 8 message.askLevel10Volume
    ++ (encodeUIntLE 8 message.bidLevel10Volume
    ++ (encodeUIntLE 8 message.lpAskLevel10Volume
    ++ (encodeUIntLE 8 message.lpBidLevel10Volume
    ++ (encodeUIntLE 8 message.totalAskVolume
    ++ (encodeUIntLE 8 message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (encodeUIntLE 8 message.estimatedTradingVolume
    ++ (Alpha.encode message.midPrice
    ++ (encodeUIntLE 8 message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (encodeUIntLE 8 message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (totalAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 8 bytes
  let (estimatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (midPrice, bytes) ← Alpha.decode 8 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, lpAskLevel1Volume, lpBidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, lpAskLevel2Volume, lpBidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, lpAskLevel3Volume, lpBidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, lpAskLevel4Volume, lpBidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, lpAskLevel5Volume, lpBidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, lpAskLevel6Volume, lpBidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, lpAskLevel7Volume, lpBidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, lpAskLevel8Volume, lpBidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, lpAskLevel9Volume, lpBidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, lpAskLevel10Volume, lpBidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length = 576 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecuritiesQuoteMmLpQuotesIncluded10LevelMessage

/-- Securities Order Filled Message: 138 bytes -/
structure SecuritiesOrderFilledMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 8
  tradingPrice : Alpha 8
  tradingVolume : BitVec 64
  openingPrice : Alpha 8
  todaysHigh : Alpha 8
  todaysLow : Alpha 8
  accumulatedTradingVolume : BitVec 64
  accumulatedTradingValue : Alpha 16
  finalAskBidTypeCode : Alpha 1
  lpHoldingQuantity : BitVec 64
  theBestAsk : Alpha 8
  theBestBid : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace SecuritiesOrderFilledMessage

def encode (message : SecuritiesOrderFilledMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.tradingPrice
    ++ (encodeUIntLE 8 message.tradingVolume
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (encodeUIntLE 8 message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (encodeUIntLE 8 message.lpHoldingQuantity
    ++ (Alpha.encode message.theBestAsk
    ++ (Alpha.encode message.theBestBid
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesOrderFilledMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 8 bytes
  let (tradingPrice, bytes) ← Alpha.decode 8 bytes
  let (tradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← Alpha.decode 8 bytes
  let (todaysHigh, bytes) ← Alpha.decode 8 bytes
  let (todaysLow, bytes) ← Alpha.decode 8 bytes
  let (accumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpHoldingQuantity, bytes) ← decodeUIntLE 8 bytes
  let (theBestAsk, bytes) ← Alpha.decode 8 bytes
  let (theBestBid, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, tradingPrice, tradingVolume, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, lpHoldingQuantity, theBestAsk, theBestBid, endKeyword }, bytes)

@[simp] theorem encode_length (message : SecuritiesOrderFilledMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecuritiesOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesOrderFilledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecuritiesOrderFilledMessage

/-- Market Operation Ts Message: 59 bytes -/
structure MarketOperationTsMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : BitVec 32
  tradingHaltReasonCode : Alpha 3
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MarketOperationTsMessage

def encode (message : MarketOperationTsMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (encodeUIntLE 4 message.boardEventGroupCode
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (encodeUIntLE 4 message.endKeyword))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationTsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← decodeUIntLE 4 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, tradingHaltReasonCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationTsMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketOperationTsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationTsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketOperationTsMessage

/-- Issue Closing Message: 83 bytes -/
structure IssueClosingMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  closingPrice : Alpha 8
  closingPriceTypeCode : Alpha 1
  upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 8
  lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession : Alpha 8
  closingPriceWeightedStockPriceAverage : Alpha 8
  closingPriceBasePriceOfBuyIn : Alpha 8
  closingPriceUpperLimitOfBuyIn : Alpha 8
  closingPriceLowerLimitOfBuyIn : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace IssueClosingMessage

def encode (message : IssueClosingMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession
    ++ (Alpha.encode message.closingPriceWeightedStockPriceAverage
    ++ (Alpha.encode message.closingPriceBasePriceOfBuyIn
    ++ (Alpha.encode message.closingPriceUpperLimitOfBuyIn
    ++ (Alpha.encode message.closingPriceLowerLimitOfBuyIn
    ++ (encodeUIntLE 4 message.endKeyword))))))))))))

def decode (bytes : List UInt8) : Option (IssueClosingMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (closingPrice, bytes) ← Alpha.decode 8 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 8 bytes
  let (lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, bytes) ← Alpha.decode 8 bytes
  let (closingPriceWeightedStockPriceAverage, bytes) ← Alpha.decode 8 bytes
  let (closingPriceBasePriceOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (closingPriceUpperLimitOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (closingPriceLowerLimitOfBuyIn, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, closingPrice, closingPriceTypeCode, upperLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, lowerLimitPriceOnTheSinglePriceTradeInTheOffHoursSession, closingPriceWeightedStockPriceAverage, closingPriceBasePriceOfBuyIn, closingPriceUpperLimitOfBuyIn, closingPriceLowerLimitOfBuyIn, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueClosingMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IssueClosingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueClosingMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IssueClosingMessage

/-- Triggering Removing Vi Message: 89 bytes -/
structure TriggeringRemovingViMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  processingTimeOfTradingSystem : Alpha 12
  theTimeEndingVi : Alpha 9
  viStatusCode : Alpha 1
  viTypeCode : Alpha 1
  aBasePriceToTriggerStaticVi : Alpha 8
  aBasePriceToTriggerDynamicVi : Alpha 8
  viTriggeringPrice : Alpha 8
  disparateRatioToTriggerStaticVi : Alpha 8
  disparateRatioToTriggerDynamicVi : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace TriggeringRemovingViMessage

def encode (message : TriggeringRemovingViMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.processingTimeOfTradingSystem
    ++ (Alpha.encode message.theTimeEndingVi
    ++ (Alpha.encode message.viStatusCode
    ++ (Alpha.encode message.viTypeCode
    ++ (Alpha.encode message.aBasePriceToTriggerStaticVi
    ++ (Alpha.encode message.aBasePriceToTriggerDynamicVi
    ++ (Alpha.encode message.viTriggeringPrice
    ++ (Alpha.encode message.disparateRatioToTriggerStaticVi
    ++ (Alpha.encode message.disparateRatioToTriggerDynamicVi
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))

def decode (bytes : List UInt8) : Option (TriggeringRemovingViMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (processingTimeOfTradingSystem, bytes) ← Alpha.decode 12 bytes
  let (theTimeEndingVi, bytes) ← Alpha.decode 9 bytes
  let (viStatusCode, bytes) ← Alpha.decode 1 bytes
  let (viTypeCode, bytes) ← Alpha.decode 1 bytes
  let (aBasePriceToTriggerStaticVi, bytes) ← Alpha.decode 8 bytes
  let (aBasePriceToTriggerDynamicVi, bytes) ← Alpha.decode 8 bytes
  let (viTriggeringPrice, bytes) ← Alpha.decode 8 bytes
  let (disparateRatioToTriggerStaticVi, bytes) ← Alpha.decode 8 bytes
  let (disparateRatioToTriggerDynamicVi, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, processingTimeOfTradingSystem, theTimeEndingVi, viStatusCode, viTypeCode, aBasePriceToTriggerStaticVi, aBasePriceToTriggerDynamicVi, viTriggeringPrice, disparateRatioToTriggerStaticVi, disparateRatioToTriggerDynamicVi, endKeyword }, bytes)

@[simp] theorem encode_length (message : TriggeringRemovingViMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TriggeringRemovingViMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TriggeringRemovingViMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TriggeringRemovingViMessage

/-- Closing Price Trading Quote Message: 42 bytes -/
structure ClosingPriceTradingQuoteMessage where
  messageSequenceNumber : BitVec 32
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  totalAskVolume : BitVec 64
  totalBidVolume : BitVec 64
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace ClosingPriceTradingQuoteMessage

def encode (message : ClosingPriceTradingQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (encodeUIntLE 8 message.totalAskVolume
    ++ (encodeUIntLE 8 message.totalBidVolume
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (ClosingPriceTradingQuoteMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (totalAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, totalAskVolume, totalBidVolume, endKeyword }, bytes)

@[simp] theorem encode_length (message : ClosingPriceTradingQuoteMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceTradingQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceTradingQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ClosingPriceTradingQuoteMessage

/-- Equities Snapshot Mm Lp Quotes Included 10 Level Message: 654 bytes -/
structure EquitiesSnapshotMmLpQuotesIncluded10LevelMessage where
  boardId : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  priceChangeAgainstPreviousDay : Alpha 1
  aPriceChangeAgainstThePreviousDay : Alpha 8
  upperLimitPrice : Alpha 8
  lowerLimitPrice : Alpha 8
  currentPrice : Alpha 8
  openingPrice : Alpha 8
  todaysHigh : Alpha 8
  todaysLow : Alpha 8
  accumulatedTradingVolume : BitVec 64
  accumulatedTradingValue : Alpha 16
  finalAskBidTypeCode : Alpha 1
  askLevel1Price : Alpha 8
  bidLevel1Price : Alpha 8
  askLevel1Volume : BitVec 64
  bidLevel1Volume : BitVec 64
  lpAskLevel1Volume : BitVec 64
  lpBidLevel1Volume : BitVec 64
  askLevel2Price : Alpha 8
  bidLevel2Price : Alpha 8
  askLevel2Volume : BitVec 64
  bidLevel2Volume : BitVec 64
  lpAskLevel2Volume : BitVec 64
  lpBidLevel2Volume : BitVec 64
  askLevel3Price : Alpha 8
  bidLevel3Price : Alpha 8
  askLevel3Volume : BitVec 64
  bidLevel3Volume : BitVec 64
  lpAskLevel3Volume : BitVec 64
  lpBidLevel3Volume : BitVec 64
  askLevel4Price : Alpha 8
  bidLevel4Price : Alpha 8
  askLevel4Volume : BitVec 64
  bidLevel4Volume : BitVec 64
  lpAskLevel4Volume : BitVec 64
  lpBidLevel4Volume : BitVec 64
  askLevel5Price : Alpha 8
  bidLevel5Price : Alpha 8
  askLevel5Volume : BitVec 64
  bidLevel5Volume : BitVec 64
  lpAskLevel5Volume : BitVec 64
  lpBidLevel5Volume : BitVec 64
  askLevel6Price : Alpha 8
  bidLevel6Price : Alpha 8
  askLevel6Volume : BitVec 64
  bidLevel6Volume : BitVec 64
  lpAskLevel6Volume : BitVec 64
  lpBidLevel6Volume : BitVec 64
  askLevel7Price : Alpha 8
  bidLevel7Price : Alpha 8
  askLevel7Volume : BitVec 64
  bidLevel7Volume : BitVec 64
  lpAskLevel7Volume : BitVec 64
  lpBidLevel7Volume : BitVec 64
  askLevel8Price : Alpha 8
  bidLevel8Price : Alpha 8
  askLevel8Volume : BitVec 64
  bidLevel8Volume : BitVec 64
  lpAskLevel8Volume : BitVec 64
  lpBidLevel8Volume : BitVec 64
  askLevel9Price : Alpha 8
  bidLevel9Price : Alpha 8
  askLevel9Volume : BitVec 64
  bidLevel9Volume : BitVec 64
  lpAskLevel9Volume : BitVec 64
  lpBidLevel9Volume : BitVec 64
  askLevel10Price : Alpha 8
  bidLevel10Price : Alpha 8
  askLevel10Volume : BitVec 64
  bidLevel10Volume : BitVec 64
  lpAskLevel10Volume : BitVec 64
  lpBidLevel10Volume : BitVec 64
  totalAskVolume : BitVec 64
  totalBidVolume : BitVec 64
  estimatedTradingPrice : Alpha 8
  estimatedTradingVolume : BitVec 64
  closingPriceTypeCode : Alpha 1
  tradingHalt : Alpha 1
  knockoutElwTypeCode : Alpha 1
  knockoutElwTriggeringTime : Alpha 9
  midPrice : Alpha 8
  totalMidPriceAskVolumeTotalAskVolumeOnMidPrice : BitVec 64
  totalMidPriceBidVolumeTotalBidVolumeOnMidPrice : BitVec 64
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace EquitiesSnapshotMmLpQuotesIncluded10LevelMessage

def encode (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.priceChangeAgainstPreviousDay
    ++ (Alpha.encode message.aPriceChangeAgainstThePreviousDay
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.currentPrice
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.todaysHigh
    ++ (Alpha.encode message.todaysLow
    ++ (encodeUIntLE 8 message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (Alpha.encode message.finalAskBidTypeCode
    ++ (Alpha.encode message.askLevel1Price
    ++ (Alpha.encode message.bidLevel1Price
    ++ (encodeUIntLE 8 message.askLevel1Volume
    ++ (encodeUIntLE 8 message.bidLevel1Volume
    ++ (encodeUIntLE 8 message.lpAskLevel1Volume
    ++ (encodeUIntLE 8 message.lpBidLevel1Volume
    ++ (Alpha.encode message.askLevel2Price
    ++ (Alpha.encode message.bidLevel2Price
    ++ (encodeUIntLE 8 message.askLevel2Volume
    ++ (encodeUIntLE 8 message.bidLevel2Volume
    ++ (encodeUIntLE 8 message.lpAskLevel2Volume
    ++ (encodeUIntLE 8 message.lpBidLevel2Volume
    ++ (Alpha.encode message.askLevel3Price
    ++ (Alpha.encode message.bidLevel3Price
    ++ (encodeUIntLE 8 message.askLevel3Volume
    ++ (encodeUIntLE 8 message.bidLevel3Volume
    ++ (encodeUIntLE 8 message.lpAskLevel3Volume
    ++ (encodeUIntLE 8 message.lpBidLevel3Volume
    ++ (Alpha.encode message.askLevel4Price
    ++ (Alpha.encode message.bidLevel4Price
    ++ (encodeUIntLE 8 message.askLevel4Volume
    ++ (encodeUIntLE 8 message.bidLevel4Volume
    ++ (encodeUIntLE 8 message.lpAskLevel4Volume
    ++ (encodeUIntLE 8 message.lpBidLevel4Volume
    ++ (Alpha.encode message.askLevel5Price
    ++ (Alpha.encode message.bidLevel5Price
    ++ (encodeUIntLE 8 message.askLevel5Volume
    ++ (encodeUIntLE 8 message.bidLevel5Volume
    ++ (encodeUIntLE 8 message.lpAskLevel5Volume
    ++ (encodeUIntLE 8 message.lpBidLevel5Volume
    ++ (Alpha.encode message.askLevel6Price
    ++ (Alpha.encode message.bidLevel6Price
    ++ (encodeUIntLE 8 message.askLevel6Volume
    ++ (encodeUIntLE 8 message.bidLevel6Volume
    ++ (encodeUIntLE 8 message.lpAskLevel6Volume
    ++ (encodeUIntLE 8 message.lpBidLevel6Volume
    ++ (Alpha.encode message.askLevel7Price
    ++ (Alpha.encode message.bidLevel7Price
    ++ (encodeUIntLE 8 message.askLevel7Volume
    ++ (encodeUIntLE 8 message.bidLevel7Volume
    ++ (encodeUIntLE 8 message.lpAskLevel7Volume
    ++ (encodeUIntLE 8 message.lpBidLevel7Volume
    ++ (Alpha.encode message.askLevel8Price
    ++ (Alpha.encode message.bidLevel8Price
    ++ (encodeUIntLE 8 message.askLevel8Volume
    ++ (encodeUIntLE 8 message.bidLevel8Volume
    ++ (encodeUIntLE 8 message.lpAskLevel8Volume
    ++ (encodeUIntLE 8 message.lpBidLevel8Volume
    ++ (Alpha.encode message.askLevel9Price
    ++ (Alpha.encode message.bidLevel9Price
    ++ (encodeUIntLE 8 message.askLevel9Volume
    ++ (encodeUIntLE 8 message.bidLevel9Volume
    ++ (encodeUIntLE 8 message.lpAskLevel9Volume
    ++ (encodeUIntLE 8 message.lpBidLevel9Volume
    ++ (Alpha.encode message.askLevel10Price
    ++ (Alpha.encode message.bidLevel10Price
    ++ (encodeUIntLE 8 message.askLevel10Volume
    ++ (encodeUIntLE 8 message.bidLevel10Volume
    ++ (encodeUIntLE 8 message.lpAskLevel10Volume
    ++ (encodeUIntLE 8 message.lpBidLevel10Volume
    ++ (encodeUIntLE 8 message.totalAskVolume
    ++ (encodeUIntLE 8 message.totalBidVolume
    ++ (Alpha.encode message.estimatedTradingPrice
    ++ (encodeUIntLE 8 message.estimatedTradingVolume
    ++ (Alpha.encode message.closingPriceTypeCode
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.knockoutElwTypeCode
    ++ (Alpha.encode message.knockoutElwTriggeringTime
    ++ (Alpha.encode message.midPrice
    ++ (encodeUIntLE 8 message.totalMidPriceAskVolumeTotalAskVolumeOnMidPrice
    ++ (encodeUIntLE 8 message.totalMidPriceBidVolumeTotalBidVolumeOnMidPrice
    ++ (encodeUIntLE 4 message.endKeyword))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesSnapshotMmLpQuotesIncluded10LevelMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (priceChangeAgainstPreviousDay, bytes) ← Alpha.decode 1 bytes
  let (aPriceChangeAgainstThePreviousDay, bytes) ← Alpha.decode 8 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 8 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 8 bytes
  let (currentPrice, bytes) ← Alpha.decode 8 bytes
  let (openingPrice, bytes) ← Alpha.decode 8 bytes
  let (todaysHigh, bytes) ← Alpha.decode 8 bytes
  let (todaysLow, bytes) ← Alpha.decode 8 bytes
  let (accumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (finalAskBidTypeCode, bytes) ← Alpha.decode 1 bytes
  let (askLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel1Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel1Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel2Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel2Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel3Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel3Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel4Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel4Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel5Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel5Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel6Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel6Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel7Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel7Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel8Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel8Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel9Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel9Volume, bytes) ← decodeUIntLE 8 bytes
  let (askLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (bidLevel10Price, bytes) ← Alpha.decode 8 bytes
  let (askLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (bidLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpAskLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (lpBidLevel10Volume, bytes) ← decodeUIntLE 8 bytes
  let (totalAskVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalBidVolume, bytes) ← decodeUIntLE 8 bytes
  let (estimatedTradingPrice, bytes) ← Alpha.decode 8 bytes
  let (estimatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceTypeCode, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (knockoutElwTypeCode, bytes) ← Alpha.decode 1 bytes
  let (knockoutElwTriggeringTime, bytes) ← Alpha.decode 9 bytes
  let (midPrice, bytes) ← Alpha.decode 8 bytes
  let (totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, bytes) ← decodeUIntLE 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ boardId, sessionId, isinCode, aDesignatedNumberForAnIssueFromKrx, priceChangeAgainstPreviousDay, aPriceChangeAgainstThePreviousDay, upperLimitPrice, lowerLimitPrice, currentPrice, openingPrice, todaysHigh, todaysLow, accumulatedTradingVolume, accumulatedTradingValue, finalAskBidTypeCode, askLevel1Price, bidLevel1Price, askLevel1Volume, bidLevel1Volume, lpAskLevel1Volume, lpBidLevel1Volume, askLevel2Price, bidLevel2Price, askLevel2Volume, bidLevel2Volume, lpAskLevel2Volume, lpBidLevel2Volume, askLevel3Price, bidLevel3Price, askLevel3Volume, bidLevel3Volume, lpAskLevel3Volume, lpBidLevel3Volume, askLevel4Price, bidLevel4Price, askLevel4Volume, bidLevel4Volume, lpAskLevel4Volume, lpBidLevel4Volume, askLevel5Price, bidLevel5Price, askLevel5Volume, bidLevel5Volume, lpAskLevel5Volume, lpBidLevel5Volume, askLevel6Price, bidLevel6Price, askLevel6Volume, bidLevel6Volume, lpAskLevel6Volume, lpBidLevel6Volume, askLevel7Price, bidLevel7Price, askLevel7Volume, bidLevel7Volume, lpAskLevel7Volume, lpBidLevel7Volume, askLevel8Price, bidLevel8Price, askLevel8Volume, bidLevel8Volume, lpAskLevel8Volume, lpBidLevel8Volume, askLevel9Price, bidLevel9Price, askLevel9Volume, bidLevel9Volume, lpAskLevel9Volume, lpBidLevel9Volume, askLevel10Price, bidLevel10Price, askLevel10Volume, bidLevel10Volume, lpAskLevel10Volume, lpBidLevel10Volume, totalAskVolume, totalBidVolume, estimatedTradingPrice, estimatedTradingVolume, closingPriceTypeCode, tradingHalt, knockoutElwTypeCode, knockoutElwTriggeringTime, midPrice, totalMidPriceAskVolumeTotalAskVolumeOnMidPrice, totalMidPriceBidVolumeTotalBidVolumeOnMidPrice, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : (encode message).length = 654 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end EquitiesSnapshotMmLpQuotesIncluded10LevelMessage

/-- Investor Activities Per Commodities Message: 62 bytes -/
structure InvestorActivitiesPerCommoditiesMessage where
  calculationTime : Alpha 6
  investorCode : Alpha 4
  accumulatedAskTradingVolume : BitVec 64
  accumulatedAskTradingValue : Alpha 16
  accumulatedBidTradingVolume : BitVec 64
  accumulatedBidTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerCommoditiesMessage

def encode (message : InvestorActivitiesPerCommoditiesMessage) : List UInt8 :=
  Alpha.encode message.calculationTime
    ++ (Alpha.encode message.investorCode
    ++ (encodeUIntLE 8 message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (encodeUIntLE 8 message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerCommoditiesMessage × List UInt8) := do
  let (calculationTime, bytes) ← Alpha.decode 6 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (accumulatedAskTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 16 bytes
  let (accumulatedBidTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ calculationTime, investorCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerCommoditiesMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : InvestorActivitiesPerCommoditiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerCommoditiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InvestorActivitiesPerCommoditiesMessage

/-- Etp Constituents Message: 203 bytes -/
structure EtpConstituentsMessage where
  messageSequenceNumber : BitVec 32
  indexCalculationInstitutionTypeCode : Alpha 2
  indexMarketClassificationId : Alpha 6
  indexSequenceNumber : Alpha 3
  indexLeverageInverseTypeCode : Alpha 2
  indexName : Alpha 80
  indexNameInEn : Alpha 80
  indexAssetClassificationId1 : Alpha 6
  indexAssetClassificationId2 : Alpha 6
  indexId : Alpha 6
  filler4 : Alpha 4
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace EtpConstituentsMessage

def encode (message : EtpConstituentsMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.indexCalculationInstitutionTypeCode
    ++ (Alpha.encode message.indexMarketClassificationId
    ++ (Alpha.encode message.indexSequenceNumber
    ++ (Alpha.encode message.indexLeverageInverseTypeCode
    ++ (Alpha.encode message.indexName
    ++ (Alpha.encode message.indexNameInEn
    ++ (Alpha.encode message.indexAssetClassificationId1
    ++ (Alpha.encode message.indexAssetClassificationId2
    ++ (Alpha.encode message.indexId
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))

def decode (bytes : List UInt8) : Option (EtpConstituentsMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (indexCalculationInstitutionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexMarketClassificationId, bytes) ← Alpha.decode 6 bytes
  let (indexSequenceNumber, bytes) ← Alpha.decode 3 bytes
  let (indexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexName, bytes) ← Alpha.decode 80 bytes
  let (indexNameInEn, bytes) ← Alpha.decode 80 bytes
  let (indexAssetClassificationId1, bytes) ← Alpha.decode 6 bytes
  let (indexAssetClassificationId2, bytes) ← Alpha.decode 6 bytes
  let (indexId, bytes) ← Alpha.decode 6 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, indexCalculationInstitutionTypeCode, indexMarketClassificationId, indexSequenceNumber, indexLeverageInverseTypeCode, indexName, indexNameInEn, indexAssetClassificationId1, indexAssetClassificationId2, indexId, filler4, endKeyword }, bytes)

@[simp] theorem encode_length (message : EtpConstituentsMessage) : (encode message).length = 203 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EtpConstituentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EtpConstituentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EtpConstituentsMessage

/-- Mm Lp Information Message: 169 bytes -/
structure MmLpInformationMessage where
  messageSequenceNumber : BitVec 32
  isinCode : Alpha 12
  marketParticipantNumber : Alpha 5
  boardId : Alpha 2
  marketMakingLpTypeCode : Alpha 1
  lpStartDate : Alpha 8
  lpEndDate : Alpha 8
  minimumOrderVolume : BitVec 64
  maximumVolumeOfMultipleOrder : BitVec 64
  bidAskSpreadUnitCode : Alpha 1
  mainMarketBidAskSpreadValue : Alpha 16
  spreadMultipleForMarketHolidays : BitVec 64
  anObligatoryTimeIntervalToPlaceAnOrder : BitVec 32
  minimumAskPrice : Alpha 16
  maximumBidPrice : Alpha 16
  minimumOrderPrice : Alpha 16
  maximumOrderPrice : Alpha 16
  extendedMarketBidAskSpreadValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MmLpInformationMessage

def encode (message : MmLpInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.marketParticipantNumber
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.marketMakingLpTypeCode
    ++ (Alpha.encode message.lpStartDate
    ++ (Alpha.encode message.lpEndDate
    ++ (encodeUIntLE 8 message.minimumOrderVolume
    ++ (encodeUIntLE 8 message.maximumVolumeOfMultipleOrder
    ++ (Alpha.encode message.bidAskSpreadUnitCode
    ++ (Alpha.encode message.mainMarketBidAskSpreadValue
    ++ (encodeUIntLE 8 message.spreadMultipleForMarketHolidays
    ++ (encodeUIntLE 4 message.anObligatoryTimeIntervalToPlaceAnOrder
    ++ (Alpha.encode message.minimumAskPrice
    ++ (Alpha.encode message.maximumBidPrice
    ++ (Alpha.encode message.minimumOrderPrice
    ++ (Alpha.encode message.maximumOrderPrice
    ++ (Alpha.encode message.extendedMarketBidAskSpreadValue
    ++ (encodeUIntLE 4 message.endKeyword))))))))))))))))))

def decode (bytes : List UInt8) : Option (MmLpInformationMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (marketParticipantNumber, bytes) ← Alpha.decode 5 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (marketMakingLpTypeCode, bytes) ← Alpha.decode 1 bytes
  let (lpStartDate, bytes) ← Alpha.decode 8 bytes
  let (lpEndDate, bytes) ← Alpha.decode 8 bytes
  let (minimumOrderVolume, bytes) ← decodeUIntLE 8 bytes
  let (maximumVolumeOfMultipleOrder, bytes) ← decodeUIntLE 8 bytes
  let (bidAskSpreadUnitCode, bytes) ← Alpha.decode 1 bytes
  let (mainMarketBidAskSpreadValue, bytes) ← Alpha.decode 16 bytes
  let (spreadMultipleForMarketHolidays, bytes) ← decodeUIntLE 8 bytes
  let (anObligatoryTimeIntervalToPlaceAnOrder, bytes) ← decodeUIntLE 4 bytes
  let (minimumAskPrice, bytes) ← Alpha.decode 16 bytes
  let (maximumBidPrice, bytes) ← Alpha.decode 16 bytes
  let (minimumOrderPrice, bytes) ← Alpha.decode 16 bytes
  let (maximumOrderPrice, bytes) ← Alpha.decode 16 bytes
  let (extendedMarketBidAskSpreadValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, isinCode, marketParticipantNumber, boardId, marketMakingLpTypeCode, lpStartDate, lpEndDate, minimumOrderVolume, maximumVolumeOfMultipleOrder, bidAskSpreadUnitCode, mainMarketBidAskSpreadValue, spreadMultipleForMarketHolidays, anObligatoryTimeIntervalToPlaceAnOrder, minimumAskPrice, maximumBidPrice, minimumOrderPrice, maximumOrderPrice, extendedMarketBidAskSpreadValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : MmLpInformationMessage) : (encode message).length = 169 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MmLpInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmLpInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MmLpInformationMessage

/-- Market Operation Schedule Message: 82 bytes -/
structure MarketOperationScheduleMessage where
  marketOperationProductId : Alpha 3
  boardId : Alpha 2
  boardEventId : Alpha 3
  startTimeOfABoardEvent : Alpha 9
  boardEventGroupCode : BitVec 32
  sessionStartEndCode : Alpha 2
  sessionId : Alpha 2
  isinCode : Alpha 12
  isinCodeOfACommonStock : Alpha 12
  productId : Alpha 11
  tradingHaltReasonCode : Alpha 3
  tradingHaltTypeCode : Alpha 1
  stepApplied : BitVec 32
  priceLimitRangeExpansionForBaseIssueTypeCode : Alpha 1
  expectedTimeOfExpandingPriceLimitRange : Alpha 9
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MarketOperationScheduleMessage

def encode (message : MarketOperationScheduleMessage) : List UInt8 :=
  Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.boardId
    ++ (Alpha.encode message.boardEventId
    ++ (Alpha.encode message.startTimeOfABoardEvent
    ++ (encodeUIntLE 4 message.boardEventGroupCode
    ++ (Alpha.encode message.sessionStartEndCode
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.isinCodeOfACommonStock
    ++ (Alpha.encode message.productId
    ++ (Alpha.encode message.tradingHaltReasonCode
    ++ (Alpha.encode message.tradingHaltTypeCode
    ++ (encodeUIntLE 4 message.stepApplied
    ++ (Alpha.encode message.priceLimitRangeExpansionForBaseIssueTypeCode
    ++ (Alpha.encode message.expectedTimeOfExpandingPriceLimitRange
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))

def decode (bytes : List UInt8) : Option (MarketOperationScheduleMessage × List UInt8) := do
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (boardEventId, bytes) ← Alpha.decode 3 bytes
  let (startTimeOfABoardEvent, bytes) ← Alpha.decode 9 bytes
  let (boardEventGroupCode, bytes) ← decodeUIntLE 4 bytes
  let (sessionStartEndCode, bytes) ← Alpha.decode 2 bytes
  let (sessionId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (isinCodeOfACommonStock, bytes) ← Alpha.decode 12 bytes
  let (productId, bytes) ← Alpha.decode 11 bytes
  let (tradingHaltReasonCode, bytes) ← Alpha.decode 3 bytes
  let (tradingHaltTypeCode, bytes) ← Alpha.decode 1 bytes
  let (stepApplied, bytes) ← decodeUIntLE 4 bytes
  let (priceLimitRangeExpansionForBaseIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expectedTimeOfExpandingPriceLimitRange, bytes) ← Alpha.decode 9 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ marketOperationProductId, boardId, boardEventId, startTimeOfABoardEvent, boardEventGroupCode, sessionStartEndCode, sessionId, isinCode, isinCodeOfACommonStock, productId, tradingHaltReasonCode, tradingHaltTypeCode, stepApplied, priceLimitRangeExpansionForBaseIssueTypeCode, expectedTimeOfExpandingPriceLimitRange, endKeyword }, bytes)

@[simp] theorem encode_length (message : MarketOperationScheduleMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketOperationScheduleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOperationScheduleMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketOperationScheduleMessage

/-- Member Firm Imposing Lifting Sanctions Message: 41 bytes -/
structure MemberFirmImposingLiftingSanctionsMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  disclosingDataTypeCode : Alpha 3
  disclosureTime : Alpha 9
  memberNumber : Alpha 5
  memberFirmTrustPrincipalTypeCode : BitVec 32
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MemberFirmImposingLiftingSanctionsMessage

def encode (message : MemberFirmImposingLiftingSanctionsMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.disclosingDataTypeCode
    ++ (Alpha.encode message.disclosureTime
    ++ (Alpha.encode message.memberNumber
    ++ (encodeUIntLE 4 message.memberFirmTrustPrincipalTypeCode
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberFirmImposingLiftingSanctionsMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (disclosingDataTypeCode, bytes) ← Alpha.decode 3 bytes
  let (disclosureTime, bytes) ← Alpha.decode 9 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (memberFirmTrustPrincipalTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, disclosingDataTypeCode, disclosureTime, memberNumber, memberFirmTrustPrincipalTypeCode, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MemberFirmImposingLiftingSanctionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberFirmImposingLiftingSanctionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MemberFirmImposingLiftingSanctionsMessage

/-- Top Five Traders Activities Message: 310 bytes -/
structure TopFiveTradersActivitiesMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  memberNumber1ForAsk : Alpha 5
  askTradingVolume1 : BitVec 64
  askTradingValue1 : Alpha 16
  memberNumber1ForBid : Alpha 5
  bidTradingVolume1 : BitVec 64
  bidTradingValue1 : Alpha 16
  memberNumber2ForAsk : Alpha 5
  askTradingVolume2 : BitVec 64
  askTradingValue2 : Alpha 16
  memberNumber2ForBid : Alpha 5
  bidTradingVolume2 : BitVec 64
  bidTradingValue2 : Alpha 16
  memberNumber3ForAsk : Alpha 5
  askTradingVolume3 : BitVec 64
  askTradingValue3 : Alpha 16
  memberNumber3ForBid : Alpha 5
  bidTradingVolume3 : BitVec 64
  bidTradingValue3 : Alpha 16
  memberNumber4ForAsk : Alpha 5
  askTradingVolume4 : BitVec 64
  askTradingValue4 : Alpha 16
  memberNumber4ForBid : Alpha 5
  bidTradingVolume4 : BitVec 64
  bidTradingValue4 : Alpha 16
  memberNumber5ForAsk : Alpha 5
  askTradingVolume5 : BitVec 64
  askTradingValue5 : Alpha 16
  memberNumber5ForBid : Alpha 5
  bidTradingVolume5 : BitVec 64
  bidTradingValue5 : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace TopFiveTradersActivitiesMessage

def encode (message : TopFiveTradersActivitiesMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.memberNumber1ForAsk
    ++ (encodeUIntLE 8 message.askTradingVolume1
    ++ (Alpha.encode message.askTradingValue1
    ++ (Alpha.encode message.memberNumber1ForBid
    ++ (encodeUIntLE 8 message.bidTradingVolume1
    ++ (Alpha.encode message.bidTradingValue1
    ++ (Alpha.encode message.memberNumber2ForAsk
    ++ (encodeUIntLE 8 message.askTradingVolume2
    ++ (Alpha.encode message.askTradingValue2
    ++ (Alpha.encode message.memberNumber2ForBid
    ++ (encodeUIntLE 8 message.bidTradingVolume2
    ++ (Alpha.encode message.bidTradingValue2
    ++ (Alpha.encode message.memberNumber3ForAsk
    ++ (encodeUIntLE 8 message.askTradingVolume3
    ++ (Alpha.encode message.askTradingValue3
    ++ (Alpha.encode message.memberNumber3ForBid
    ++ (encodeUIntLE 8 message.bidTradingVolume3
    ++ (Alpha.encode message.bidTradingValue3
    ++ (Alpha.encode message.memberNumber4ForAsk
    ++ (encodeUIntLE 8 message.askTradingVolume4
    ++ (Alpha.encode message.askTradingValue4
    ++ (Alpha.encode message.memberNumber4ForBid
    ++ (encodeUIntLE 8 message.bidTradingVolume4
    ++ (Alpha.encode message.bidTradingValue4
    ++ (Alpha.encode message.memberNumber5ForAsk
    ++ (encodeUIntLE 8 message.askTradingVolume5
    ++ (Alpha.encode message.askTradingValue5
    ++ (Alpha.encode message.memberNumber5ForBid
    ++ (encodeUIntLE 8 message.bidTradingVolume5
    ++ (Alpha.encode message.bidTradingValue5
    ++ (encodeUIntLE 4 message.endKeyword))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TopFiveTradersActivitiesMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (memberNumber1ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume1, bytes) ← decodeUIntLE 8 bytes
  let (askTradingValue1, bytes) ← Alpha.decode 16 bytes
  let (memberNumber1ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume1, bytes) ← decodeUIntLE 8 bytes
  let (bidTradingValue1, bytes) ← Alpha.decode 16 bytes
  let (memberNumber2ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume2, bytes) ← decodeUIntLE 8 bytes
  let (askTradingValue2, bytes) ← Alpha.decode 16 bytes
  let (memberNumber2ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume2, bytes) ← decodeUIntLE 8 bytes
  let (bidTradingValue2, bytes) ← Alpha.decode 16 bytes
  let (memberNumber3ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume3, bytes) ← decodeUIntLE 8 bytes
  let (askTradingValue3, bytes) ← Alpha.decode 16 bytes
  let (memberNumber3ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume3, bytes) ← decodeUIntLE 8 bytes
  let (bidTradingValue3, bytes) ← Alpha.decode 16 bytes
  let (memberNumber4ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume4, bytes) ← decodeUIntLE 8 bytes
  let (askTradingValue4, bytes) ← Alpha.decode 16 bytes
  let (memberNumber4ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume4, bytes) ← decodeUIntLE 8 bytes
  let (bidTradingValue4, bytes) ← Alpha.decode 16 bytes
  let (memberNumber5ForAsk, bytes) ← Alpha.decode 5 bytes
  let (askTradingVolume5, bytes) ← decodeUIntLE 8 bytes
  let (askTradingValue5, bytes) ← Alpha.decode 16 bytes
  let (memberNumber5ForBid, bytes) ← Alpha.decode 5 bytes
  let (bidTradingVolume5, bytes) ← decodeUIntLE 8 bytes
  let (bidTradingValue5, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, memberNumber1ForAsk, askTradingVolume1, askTradingValue1, memberNumber1ForBid, bidTradingVolume1, bidTradingValue1, memberNumber2ForAsk, askTradingVolume2, askTradingValue2, memberNumber2ForBid, bidTradingVolume2, bidTradingValue2, memberNumber3ForAsk, askTradingVolume3, askTradingValue3, memberNumber3ForBid, bidTradingVolume3, bidTradingValue3, memberNumber4ForAsk, askTradingVolume4, askTradingValue4, memberNumber4ForBid, bidTradingVolume4, bidTradingValue4, memberNumber5ForAsk, askTradingVolume5, askTradingValue5, memberNumber5ForBid, bidTradingVolume5, bidTradingValue5, endKeyword }, bytes)

@[simp] theorem encode_length (message : TopFiveTradersActivitiesMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TopFiveTradersActivitiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TopFiveTradersActivitiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopFiveTradersActivitiesMessage

/-- Equities Batch Data Message: 551 bytes -/
structure EquitiesBatchDataMessage where
  messageSequenceNumber : BitVec 32
  totalNumberOfInstrumentsOfTheContract : BitVec 32
  businessDate : Alpha 8
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  abbreviatedIssueCode : Alpha 9
  abbreviatedIssueName : Alpha 40
  abbreviatedIssueNameInEn : Alpha 40
  groupNumber : Alpha 5
  marketOperationProductId : Alpha 3
  securityGroupId : Alpha 2
  unitTrading : Alpha 1
  rightsTypeCode : Alpha 2
  parValueTypeCode : Alpha 2
  anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice : Alpha 1
  reevaluationReasonCode : Alpha 2
  basePriceChange : Alpha 1
  randomEndTriggerCode : Alpha 1
  marketAlert : Alpha 1
  marketAlertTypeCode : Alpha 2
  koreaCorporateGovernanceStockPriceIndexKogi : Alpha 1
  issueForAdministration : Alpha 1
  unfaithfulDisclosure : Alpha 1
  backdoorListing : Alpha 1
  tradingHalt : Alpha 1
  industryId : Alpha 10
  smallMediumSizedBusiness : Alpha 1
  sectionTypeCode : Alpha 1
  investmentInstitutionTypeCode : Alpha 1
  basePrice : Alpha 8
  yesterdaysClosingPriceTypeCodeKrx : Alpha 1
  yesterdaysClosingPriceKrx : Alpha 8
  yesterdaysAccumulatedTradingAmount : BitVec 64
  yesterdaysAccumulatedTradingValue : Alpha 16
  upperLimitPrice : Alpha 8
  lowerLimitPrice : Alpha 8
  substitutePriceOfSecurities : Alpha 8
  parValue : Alpha 8
  issuingPrice : Alpha 8
  listingDate : Alpha 8
  numberOfListedShares : BitVec 64
  liquidationTrade : Alpha 1
  theEstablishmentDate : Alpha 8
  maturityDate : Alpha 8
  exercisingPeriod : Alpha 8
  expirationDateForRight : Alpha 8
  exercisePriceOfElwOrBw : Alpha 8
  capital : Alpha 16
  creditOrderPossibility : Alpha 1
  limitOrderPermissionTypeCode : BitVec 32
  marketPriceOrderPermissionTypeCode : BitVec 32
  conditionedOrderPermissionTypeCode : BitVec 32
  bestFavorableOrderPermissionTypeCode : BitVec 32
  firstBestOrderPermissionType : BitVec 32
  midPriceOrderPermissionTypeCode : BitVec 32
  stopLimitPriceOrderPermissionTypeCode : BitVec 32
  capitalIncreaseTypeCode : Alpha 2
  otherStockTypeCode : Alpha 1
  nationalStock : Alpha 1
  appraisedPrice : Alpha 8
  lowestOrderPrice : Alpha 8
  highestOrderPrice : Alpha 8
  unitOfVolumeInMainBoard : BitVec 64
  lotSizeAfterhoursTrading : BitVec 64
  reiTsTypeCode : Alpha 1
  targetStockIsinCode : Alpha 12
  currencyIsoCode : Alpha 3
  countryCode : Alpha 3
  marketMakingPossibility : Alpha 1
  closingPriceTradingPossibilityInTheAfterHours : Alpha 1
  closingPriceTradingInThePreopeningMarket : Alpha 1
  blockTradingInThePreopeningMarket : Alpha 1
  basketTradingInThePreopeningMarket : Alpha 1
  announcementOfEstimatedTradingPrice : Alpha 1
  shortSelling : Alpha 1
  etfTrackingDifference : Alpha 8
  regs : Alpha 1
  spac : Alpha 1
  taxTypeCode : Alpha 1
  appraisalRatioOfSubstitutePrice : Alpha 8
  investmentCautionIssue : Alpha 1
  delistingDate : Alpha 8
  shorttermOverheatIssueTypeCode : Alpha 1
  etfReplicationMethodsTypeCode : Alpha 1
  expirationDate : Alpha 8
  distributionTypeCode : Alpha 2
  calculationOfRedemptionPriceStartDate : Alpha 8
  calculationOfRedemptionPriceEndDate : Alpha 8
  etpProductTypeCode : Alpha 1
  indexCalculationInstitutionTypeCode : Alpha 2
  indexMarketClassificationId : Alpha 6
  indexSequenceNumber : Alpha 3
  trackingIndexLeverageInverseTypeCode : Alpha 2
  referenceIndexLeverageInverseTypeCode : Alpha 2
  indexAssetClassificationId1 : Alpha 6
  indexAssetClassificationId2 : Alpha 6
  ipoUnderwriterMemberNumber : Alpha 5
  lpOrder : Alpha 1
  lowLiquidity : Alpha 1
  abnormalRise : Alpha 1
  upperLimitQuantity : Alpha 16
  investmentPrecautionIssue : Alpha 1
  preferredStocksWithLesserShares : Alpha 1
  spacMerger : Alpha 1
  segmentTypeCode : Alpha 1
  afterMarketPossibility : Alpha 1
  choiceOnCompetitiveTrading : Alpha 1
  limitOnCompetitiveTradingVolume : Alpha 1
  occurrenceOfReasonsProhibitingCompetitiveTrading : Alpha 1
  approvalOnCompetitiveTrading : Alpha 1
  approvalOnNegotiationTrading : Alpha 1
  yesterdaysClosingPriceTypeCodeNxt : Alpha 1
  yesterdaysClosingPriceNxt : Alpha 8
  competitionBoardTradePermissionCode : BitVec 32
  negotiationPossibleOrNotBeforeMainMarket : Alpha 1
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace EquitiesBatchDataMessage

def encode (message : EquitiesBatchDataMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (encodeUIntLE 4 message.totalNumberOfInstrumentsOfTheContract
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.abbreviatedIssueCode
    ++ (Alpha.encode message.abbreviatedIssueName
    ++ (Alpha.encode message.abbreviatedIssueNameInEn
    ++ (Alpha.encode message.groupNumber
    ++ (Alpha.encode message.marketOperationProductId
    ++ (Alpha.encode message.securityGroupId
    ++ (Alpha.encode message.unitTrading
    ++ (Alpha.encode message.rightsTypeCode
    ++ (Alpha.encode message.parValueTypeCode
    ++ (Alpha.encode message.anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice
    ++ (Alpha.encode message.reevaluationReasonCode
    ++ (Alpha.encode message.basePriceChange
    ++ (Alpha.encode message.randomEndTriggerCode
    ++ (Alpha.encode message.marketAlert
    ++ (Alpha.encode message.marketAlertTypeCode
    ++ (Alpha.encode message.koreaCorporateGovernanceStockPriceIndexKogi
    ++ (Alpha.encode message.issueForAdministration
    ++ (Alpha.encode message.unfaithfulDisclosure
    ++ (Alpha.encode message.backdoorListing
    ++ (Alpha.encode message.tradingHalt
    ++ (Alpha.encode message.industryId
    ++ (Alpha.encode message.smallMediumSizedBusiness
    ++ (Alpha.encode message.sectionTypeCode
    ++ (Alpha.encode message.investmentInstitutionTypeCode
    ++ (Alpha.encode message.basePrice
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeKrx
    ++ (Alpha.encode message.yesterdaysClosingPriceKrx
    ++ (encodeUIntLE 8 message.yesterdaysAccumulatedTradingAmount
    ++ (Alpha.encode message.yesterdaysAccumulatedTradingValue
    ++ (Alpha.encode message.upperLimitPrice
    ++ (Alpha.encode message.lowerLimitPrice
    ++ (Alpha.encode message.substitutePriceOfSecurities
    ++ (Alpha.encode message.parValue
    ++ (Alpha.encode message.issuingPrice
    ++ (Alpha.encode message.listingDate
    ++ (encodeUIntLE 8 message.numberOfListedShares
    ++ (Alpha.encode message.liquidationTrade
    ++ (Alpha.encode message.theEstablishmentDate
    ++ (Alpha.encode message.maturityDate
    ++ (Alpha.encode message.exercisingPeriod
    ++ (Alpha.encode message.expirationDateForRight
    ++ (Alpha.encode message.exercisePriceOfElwOrBw
    ++ (Alpha.encode message.capital
    ++ (Alpha.encode message.creditOrderPossibility
    ++ (encodeUIntLE 4 message.limitOrderPermissionTypeCode
    ++ (encodeUIntLE 4 message.marketPriceOrderPermissionTypeCode
    ++ (encodeUIntLE 4 message.conditionedOrderPermissionTypeCode
    ++ (encodeUIntLE 4 message.bestFavorableOrderPermissionTypeCode
    ++ (encodeUIntLE 4 message.firstBestOrderPermissionType
    ++ (encodeUIntLE 4 message.midPriceOrderPermissionTypeCode
    ++ (encodeUIntLE 4 message.stopLimitPriceOrderPermissionTypeCode
    ++ (Alpha.encode message.capitalIncreaseTypeCode
    ++ (Alpha.encode message.otherStockTypeCode
    ++ (Alpha.encode message.nationalStock
    ++ (Alpha.encode message.appraisedPrice
    ++ (Alpha.encode message.lowestOrderPrice
    ++ (Alpha.encode message.highestOrderPrice
    ++ (encodeUIntLE 8 message.unitOfVolumeInMainBoard
    ++ (encodeUIntLE 8 message.lotSizeAfterhoursTrading
    ++ (Alpha.encode message.reiTsTypeCode
    ++ (Alpha.encode message.targetStockIsinCode
    ++ (Alpha.encode message.currencyIsoCode
    ++ (Alpha.encode message.countryCode
    ++ (Alpha.encode message.marketMakingPossibility
    ++ (Alpha.encode message.closingPriceTradingPossibilityInTheAfterHours
    ++ (Alpha.encode message.closingPriceTradingInThePreopeningMarket
    ++ (Alpha.encode message.blockTradingInThePreopeningMarket
    ++ (Alpha.encode message.basketTradingInThePreopeningMarket
    ++ (Alpha.encode message.announcementOfEstimatedTradingPrice
    ++ (Alpha.encode message.shortSelling
    ++ (Alpha.encode message.etfTrackingDifference
    ++ (Alpha.encode message.regs
    ++ (Alpha.encode message.spac
    ++ (Alpha.encode message.taxTypeCode
    ++ (Alpha.encode message.appraisalRatioOfSubstitutePrice
    ++ (Alpha.encode message.investmentCautionIssue
    ++ (Alpha.encode message.delistingDate
    ++ (Alpha.encode message.shorttermOverheatIssueTypeCode
    ++ (Alpha.encode message.etfReplicationMethodsTypeCode
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.distributionTypeCode
    ++ (Alpha.encode message.calculationOfRedemptionPriceStartDate
    ++ (Alpha.encode message.calculationOfRedemptionPriceEndDate
    ++ (Alpha.encode message.etpProductTypeCode
    ++ (Alpha.encode message.indexCalculationInstitutionTypeCode
    ++ (Alpha.encode message.indexMarketClassificationId
    ++ (Alpha.encode message.indexSequenceNumber
    ++ (Alpha.encode message.trackingIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.referenceIndexLeverageInverseTypeCode
    ++ (Alpha.encode message.indexAssetClassificationId1
    ++ (Alpha.encode message.indexAssetClassificationId2
    ++ (Alpha.encode message.ipoUnderwriterMemberNumber
    ++ (Alpha.encode message.lpOrder
    ++ (Alpha.encode message.lowLiquidity
    ++ (Alpha.encode message.abnormalRise
    ++ (Alpha.encode message.upperLimitQuantity
    ++ (Alpha.encode message.investmentPrecautionIssue
    ++ (Alpha.encode message.preferredStocksWithLesserShares
    ++ (Alpha.encode message.spacMerger
    ++ (Alpha.encode message.segmentTypeCode
    ++ (Alpha.encode message.afterMarketPossibility
    ++ (Alpha.encode message.choiceOnCompetitiveTrading
    ++ (Alpha.encode message.limitOnCompetitiveTradingVolume
    ++ (Alpha.encode message.occurrenceOfReasonsProhibitingCompetitiveTrading
    ++ (Alpha.encode message.approvalOnCompetitiveTrading
    ++ (Alpha.encode message.approvalOnNegotiationTrading
    ++ (Alpha.encode message.yesterdaysClosingPriceTypeCodeNxt
    ++ (Alpha.encode message.yesterdaysClosingPriceNxt
    ++ (encodeUIntLE 4 message.competitionBoardTradePermissionCode
    ++ (Alpha.encode message.negotiationPossibleOrNotBeforeMainMarket
    ++ (encodeUIntLE 4 message.endKeyword)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EquitiesBatchDataMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (totalNumberOfInstrumentsOfTheContract, bytes) ← decodeUIntLE 4 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (abbreviatedIssueCode, bytes) ← Alpha.decode 9 bytes
  let (abbreviatedIssueName, bytes) ← Alpha.decode 40 bytes
  let (abbreviatedIssueNameInEn, bytes) ← Alpha.decode 40 bytes
  let (groupNumber, bytes) ← Alpha.decode 5 bytes
  let (marketOperationProductId, bytes) ← Alpha.decode 3 bytes
  let (securityGroupId, bytes) ← Alpha.decode 2 bytes
  let (unitTrading, bytes) ← Alpha.decode 1 bytes
  let (rightsTypeCode, bytes) ← Alpha.decode 2 bytes
  let (parValueTypeCode, bytes) ← Alpha.decode 2 bytes
  let (anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, bytes) ← Alpha.decode 1 bytes
  let (reevaluationReasonCode, bytes) ← Alpha.decode 2 bytes
  let (basePriceChange, bytes) ← Alpha.decode 1 bytes
  let (randomEndTriggerCode, bytes) ← Alpha.decode 1 bytes
  let (marketAlert, bytes) ← Alpha.decode 1 bytes
  let (marketAlertTypeCode, bytes) ← Alpha.decode 2 bytes
  let (koreaCorporateGovernanceStockPriceIndexKogi, bytes) ← Alpha.decode 1 bytes
  let (issueForAdministration, bytes) ← Alpha.decode 1 bytes
  let (unfaithfulDisclosure, bytes) ← Alpha.decode 1 bytes
  let (backdoorListing, bytes) ← Alpha.decode 1 bytes
  let (tradingHalt, bytes) ← Alpha.decode 1 bytes
  let (industryId, bytes) ← Alpha.decode 10 bytes
  let (smallMediumSizedBusiness, bytes) ← Alpha.decode 1 bytes
  let (sectionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (investmentInstitutionTypeCode, bytes) ← Alpha.decode 1 bytes
  let (basePrice, bytes) ← Alpha.decode 8 bytes
  let (yesterdaysClosingPriceTypeCodeKrx, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceKrx, bytes) ← Alpha.decode 8 bytes
  let (yesterdaysAccumulatedTradingAmount, bytes) ← decodeUIntLE 8 bytes
  let (yesterdaysAccumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (upperLimitPrice, bytes) ← Alpha.decode 8 bytes
  let (lowerLimitPrice, bytes) ← Alpha.decode 8 bytes
  let (substitutePriceOfSecurities, bytes) ← Alpha.decode 8 bytes
  let (parValue, bytes) ← Alpha.decode 8 bytes
  let (issuingPrice, bytes) ← Alpha.decode 8 bytes
  let (listingDate, bytes) ← Alpha.decode 8 bytes
  let (numberOfListedShares, bytes) ← decodeUIntLE 8 bytes
  let (liquidationTrade, bytes) ← Alpha.decode 1 bytes
  let (theEstablishmentDate, bytes) ← Alpha.decode 8 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (exercisingPeriod, bytes) ← Alpha.decode 8 bytes
  let (expirationDateForRight, bytes) ← Alpha.decode 8 bytes
  let (exercisePriceOfElwOrBw, bytes) ← Alpha.decode 8 bytes
  let (capital, bytes) ← Alpha.decode 16 bytes
  let (creditOrderPossibility, bytes) ← Alpha.decode 1 bytes
  let (limitOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (marketPriceOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (conditionedOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (bestFavorableOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (firstBestOrderPermissionType, bytes) ← decodeUIntLE 4 bytes
  let (midPriceOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (stopLimitPriceOrderPermissionTypeCode, bytes) ← decodeUIntLE 4 bytes
  let (capitalIncreaseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (otherStockTypeCode, bytes) ← Alpha.decode 1 bytes
  let (nationalStock, bytes) ← Alpha.decode 1 bytes
  let (appraisedPrice, bytes) ← Alpha.decode 8 bytes
  let (lowestOrderPrice, bytes) ← Alpha.decode 8 bytes
  let (highestOrderPrice, bytes) ← Alpha.decode 8 bytes
  let (unitOfVolumeInMainBoard, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeAfterhoursTrading, bytes) ← decodeUIntLE 8 bytes
  let (reiTsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (targetStockIsinCode, bytes) ← Alpha.decode 12 bytes
  let (currencyIsoCode, bytes) ← Alpha.decode 3 bytes
  let (countryCode, bytes) ← Alpha.decode 3 bytes
  let (marketMakingPossibility, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingPossibilityInTheAfterHours, bytes) ← Alpha.decode 1 bytes
  let (closingPriceTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (blockTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (basketTradingInThePreopeningMarket, bytes) ← Alpha.decode 1 bytes
  let (announcementOfEstimatedTradingPrice, bytes) ← Alpha.decode 1 bytes
  let (shortSelling, bytes) ← Alpha.decode 1 bytes
  let (etfTrackingDifference, bytes) ← Alpha.decode 8 bytes
  let (regs, bytes) ← Alpha.decode 1 bytes
  let (spac, bytes) ← Alpha.decode 1 bytes
  let (taxTypeCode, bytes) ← Alpha.decode 1 bytes
  let (appraisalRatioOfSubstitutePrice, bytes) ← Alpha.decode 8 bytes
  let (investmentCautionIssue, bytes) ← Alpha.decode 1 bytes
  let (delistingDate, bytes) ← Alpha.decode 8 bytes
  let (shorttermOverheatIssueTypeCode, bytes) ← Alpha.decode 1 bytes
  let (etfReplicationMethodsTypeCode, bytes) ← Alpha.decode 1 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (distributionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (calculationOfRedemptionPriceStartDate, bytes) ← Alpha.decode 8 bytes
  let (calculationOfRedemptionPriceEndDate, bytes) ← Alpha.decode 8 bytes
  let (etpProductTypeCode, bytes) ← Alpha.decode 1 bytes
  let (indexCalculationInstitutionTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexMarketClassificationId, bytes) ← Alpha.decode 6 bytes
  let (indexSequenceNumber, bytes) ← Alpha.decode 3 bytes
  let (trackingIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (referenceIndexLeverageInverseTypeCode, bytes) ← Alpha.decode 2 bytes
  let (indexAssetClassificationId1, bytes) ← Alpha.decode 6 bytes
  let (indexAssetClassificationId2, bytes) ← Alpha.decode 6 bytes
  let (ipoUnderwriterMemberNumber, bytes) ← Alpha.decode 5 bytes
  let (lpOrder, bytes) ← Alpha.decode 1 bytes
  let (lowLiquidity, bytes) ← Alpha.decode 1 bytes
  let (abnormalRise, bytes) ← Alpha.decode 1 bytes
  let (upperLimitQuantity, bytes) ← Alpha.decode 16 bytes
  let (investmentPrecautionIssue, bytes) ← Alpha.decode 1 bytes
  let (preferredStocksWithLesserShares, bytes) ← Alpha.decode 1 bytes
  let (spacMerger, bytes) ← Alpha.decode 1 bytes
  let (segmentTypeCode, bytes) ← Alpha.decode 1 bytes
  let (afterMarketPossibility, bytes) ← Alpha.decode 1 bytes
  let (choiceOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (limitOnCompetitiveTradingVolume, bytes) ← Alpha.decode 1 bytes
  let (occurrenceOfReasonsProhibitingCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnCompetitiveTrading, bytes) ← Alpha.decode 1 bytes
  let (approvalOnNegotiationTrading, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceTypeCodeNxt, bytes) ← Alpha.decode 1 bytes
  let (yesterdaysClosingPriceNxt, bytes) ← Alpha.decode 8 bytes
  let (competitionBoardTradePermissionCode, bytes) ← decodeUIntLE 4 bytes
  let (negotiationPossibleOrNotBeforeMainMarket, bytes) ← Alpha.decode 1 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, totalNumberOfInstrumentsOfTheContract, businessDate, isinCode, aDesignatedNumberForAnIssueFromKrx, abbreviatedIssueCode, abbreviatedIssueName, abbreviatedIssueNameInEn, groupNumber, marketOperationProductId, securityGroupId, unitTrading, rightsTypeCode, parValueTypeCode, anIssueOfWhichBasePriceIsSettledWithATodaysSinglePrice, reevaluationReasonCode, basePriceChange, randomEndTriggerCode, marketAlert, marketAlertTypeCode, koreaCorporateGovernanceStockPriceIndexKogi, issueForAdministration, unfaithfulDisclosure, backdoorListing, tradingHalt, industryId, smallMediumSizedBusiness, sectionTypeCode, investmentInstitutionTypeCode, basePrice, yesterdaysClosingPriceTypeCodeKrx, yesterdaysClosingPriceKrx, yesterdaysAccumulatedTradingAmount, yesterdaysAccumulatedTradingValue, upperLimitPrice, lowerLimitPrice, substitutePriceOfSecurities, parValue, issuingPrice, listingDate, numberOfListedShares, liquidationTrade, theEstablishmentDate, maturityDate, exercisingPeriod, expirationDateForRight, exercisePriceOfElwOrBw, capital, creditOrderPossibility, limitOrderPermissionTypeCode, marketPriceOrderPermissionTypeCode, conditionedOrderPermissionTypeCode, bestFavorableOrderPermissionTypeCode, firstBestOrderPermissionType, midPriceOrderPermissionTypeCode, stopLimitPriceOrderPermissionTypeCode, capitalIncreaseTypeCode, otherStockTypeCode, nationalStock, appraisedPrice, lowestOrderPrice, highestOrderPrice, unitOfVolumeInMainBoard, lotSizeAfterhoursTrading, reiTsTypeCode, targetStockIsinCode, currencyIsoCode, countryCode, marketMakingPossibility, closingPriceTradingPossibilityInTheAfterHours, closingPriceTradingInThePreopeningMarket, blockTradingInThePreopeningMarket, basketTradingInThePreopeningMarket, announcementOfEstimatedTradingPrice, shortSelling, etfTrackingDifference, regs, spac, taxTypeCode, appraisalRatioOfSubstitutePrice, investmentCautionIssue, delistingDate, shorttermOverheatIssueTypeCode, etfReplicationMethodsTypeCode, expirationDate, distributionTypeCode, calculationOfRedemptionPriceStartDate, calculationOfRedemptionPriceEndDate, etpProductTypeCode, indexCalculationInstitutionTypeCode, indexMarketClassificationId, indexSequenceNumber, trackingIndexLeverageInverseTypeCode, referenceIndexLeverageInverseTypeCode, indexAssetClassificationId1, indexAssetClassificationId2, ipoUnderwriterMemberNumber, lpOrder, lowLiquidity, abnormalRise, upperLimitQuantity, investmentPrecautionIssue, preferredStocksWithLesserShares, spacMerger, segmentTypeCode, afterMarketPossibility, choiceOnCompetitiveTrading, limitOnCompetitiveTradingVolume, occurrenceOfReasonsProhibitingCompetitiveTrading, approvalOnCompetitiveTrading, approvalOnNegotiationTrading, yesterdaysClosingPriceTypeCodeNxt, yesterdaysClosingPriceNxt, competitionBoardTradePermissionCode, negotiationPossibleOrNotBeforeMainMarket, endKeyword }, bytes)

@[simp] theorem encode_length (message : EquitiesBatchDataMessage) : (encode message).length = 551 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesBatchDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EquitiesBatchDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EquitiesBatchDataMessage

/-- Member Information Message: 201 bytes -/
structure MemberInformationMessage where
  messageSequenceNumber : BitVec 32
  businessDate : Alpha 8
  marketParticipantNumber : Alpha 5
  nameOfAMarketParticipantInKr : Alpha 80
  nameOfAMarketParticipantInEn : Alpha 80
  anAbbreviatedNameOfAMarketParticipantInKr : Alpha 20
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace MemberInformationMessage

def encode (message : MemberInformationMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.businessDate
    ++ (Alpha.encode message.marketParticipantNumber
    ++ (Alpha.encode message.nameOfAMarketParticipantInKr
    ++ (Alpha.encode message.nameOfAMarketParticipantInEn
    ++ (Alpha.encode message.anAbbreviatedNameOfAMarketParticipantInKr
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (MemberInformationMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  let (marketParticipantNumber, bytes) ← Alpha.decode 5 bytes
  let (nameOfAMarketParticipantInKr, bytes) ← Alpha.decode 80 bytes
  let (nameOfAMarketParticipantInEn, bytes) ← Alpha.decode 80 bytes
  let (anAbbreviatedNameOfAMarketParticipantInKr, bytes) ← Alpha.decode 20 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, businessDate, marketParticipantNumber, nameOfAMarketParticipantInKr, nameOfAMarketParticipantInEn, anAbbreviatedNameOfAMarketParticipantInKr, endKeyword }, bytes)

@[simp] theorem encode_length (message : MemberInformationMessage) : (encode message).length = 201 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MemberInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MemberInformationMessage

/-- Issue Event Message: 42 bytes -/
structure IssueEventMessage where
  messageSequenceNumber : BitVec 32
  isinCode : Alpha 12
  eventTypeCode : Alpha 2
  eventReasonCode : Alpha 4
  eventStartDate : Alpha 8
  eventEndDate : Alpha 8
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace IssueEventMessage

def encode (message : IssueEventMessage) : List UInt8 :=
  encodeUIntLE 4 message.messageSequenceNumber
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.eventTypeCode
    ++ (Alpha.encode message.eventReasonCode
    ++ (Alpha.encode message.eventStartDate
    ++ (Alpha.encode message.eventEndDate
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (IssueEventMessage × List UInt8) := do
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (eventTypeCode, bytes) ← Alpha.decode 2 bytes
  let (eventReasonCode, bytes) ← Alpha.decode 4 bytes
  let (eventStartDate, bytes) ← Alpha.decode 8 bytes
  let (eventEndDate, bytes) ← Alpha.decode 8 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ messageSequenceNumber, isinCode, eventTypeCode, eventReasonCode, eventStartDate, eventEndDate, endKeyword }, bytes)

@[simp] theorem encode_length (message : IssueEventMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IssueEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IssueEventMessage

/-- Block Basket Trade Data Message: 46 bytes -/
structure BlockBasketTradeDataMessage where
  boardId : Alpha 2
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  accumulatedTradingVolume : BitVec 64
  accumulatedTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace BlockBasketTradeDataMessage

def encode (message : BlockBasketTradeDataMessage) : List UInt8 :=
  Alpha.encode message.boardId
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (encodeUIntLE 8 message.accumulatedTradingVolume
    ++ (Alpha.encode message.accumulatedTradingValue
    ++ (encodeUIntLE 4 message.endKeyword)))))

def decode (bytes : List UInt8) : Option (BlockBasketTradeDataMessage × List UInt8) := do
  let (boardId, bytes) ← Alpha.decode 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (accumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ boardId, isinCode, aDesignatedNumberForAnIssueFromKrx, accumulatedTradingVolume, accumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BlockBasketTradeDataMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BlockBasketTradeDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockBasketTradeDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BlockBasketTradeDataMessage

/-- Investor Activities Per An Issue Eod Message: 72 bytes -/
structure InvestorActivitiesPerAnIssueEodMessage where
  isinCode : Alpha 12
  aDesignatedNumberForAnIssueFromKrx : BitVec 32
  investorCode : Alpha 4
  accumulatedAskTradingVolume : BitVec 64
  accumulatedAskTradingValue : Alpha 16
  accumulatedBidTradingVolume : BitVec 64
  accumulatedBidTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace InvestorActivitiesPerAnIssueEodMessage

def encode (message : InvestorActivitiesPerAnIssueEodMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.aDesignatedNumberForAnIssueFromKrx
    ++ (Alpha.encode message.investorCode
    ++ (encodeUIntLE 8 message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (encodeUIntLE 8 message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (encodeUIntLE 4 message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (InvestorActivitiesPerAnIssueEodMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (aDesignatedNumberForAnIssueFromKrx, bytes) ← decodeUIntLE 4 bytes
  let (investorCode, bytes) ← Alpha.decode 4 bytes
  let (accumulatedAskTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 16 bytes
  let (accumulatedBidTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, aDesignatedNumberForAnIssueFromKrx, investorCode, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : InvestorActivitiesPerAnIssueEodMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestorActivitiesPerAnIssueEodMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InvestorActivitiesPerAnIssueEodMessage

/-- Short Selling Message: 88 bytes -/
structure ShortSellingMessage where
  isinCode : Alpha 12
  coveredShortSellingTradingVolume : BitVec 64
  coveredShortSellingTradingValue : Alpha 16
  uptickRuleAppliedCoveredShortSellingTradingVolume : BitVec 64
  uptickRuleAppliedCoveredShortSellingTradingValue : Alpha 16
  uptickRuleUnappliedCoveredShortSellingTradingVolume : BitVec 64
  uptickRuleUnappliedCoveredShortSellingTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace ShortSellingMessage

def encode (message : ShortSellingMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (encodeUIntLE 8 message.coveredShortSellingTradingVolume
    ++ (Alpha.encode message.coveredShortSellingTradingValue
    ++ (encodeUIntLE 8 message.uptickRuleAppliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleAppliedCoveredShortSellingTradingValue
    ++ (encodeUIntLE 8 message.uptickRuleUnappliedCoveredShortSellingTradingVolume
    ++ (Alpha.encode message.uptickRuleUnappliedCoveredShortSellingTradingValue
    ++ (encodeUIntLE 4 message.endKeyword)))))))

def decode (bytes : List UInt8) : Option (ShortSellingMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (coveredShortSellingTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (coveredShortSellingTradingValue, bytes) ← Alpha.decode 16 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (uptickRuleAppliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 16 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (uptickRuleUnappliedCoveredShortSellingTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, coveredShortSellingTradingVolume, coveredShortSellingTradingValue, uptickRuleAppliedCoveredShortSellingTradingVolume, uptickRuleAppliedCoveredShortSellingTradingValue, uptickRuleUnappliedCoveredShortSellingTradingVolume, uptickRuleUnappliedCoveredShortSellingTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : ShortSellingMessage) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ShortSellingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSellingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ShortSellingMessage

/-- Brokers Acitity Information Message: 69 bytes -/
structure BrokersAcitityInformationMessage where
  isinCode : Alpha 12
  memberNumber : Alpha 5
  accumulatedAskTradingVolume : BitVec 64
  accumulatedAskTradingValue : Alpha 16
  accumulatedBidTradingVolume : BitVec 64
  accumulatedBidTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace BrokersAcitityInformationMessage

def encode (message : BrokersAcitityInformationMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (Alpha.encode message.memberNumber
    ++ (encodeUIntLE 8 message.accumulatedAskTradingVolume
    ++ (Alpha.encode message.accumulatedAskTradingValue
    ++ (encodeUIntLE 8 message.accumulatedBidTradingVolume
    ++ (Alpha.encode message.accumulatedBidTradingValue
    ++ (encodeUIntLE 4 message.endKeyword))))))

def decode (bytes : List UInt8) : Option (BrokersAcitityInformationMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (memberNumber, bytes) ← Alpha.decode 5 bytes
  let (accumulatedAskTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedAskTradingValue, bytes) ← Alpha.decode 16 bytes
  let (accumulatedBidTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (accumulatedBidTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, memberNumber, accumulatedAskTradingVolume, accumulatedAskTradingValue, accumulatedBidTradingVolume, accumulatedBidTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : BrokersAcitityInformationMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BrokersAcitityInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokersAcitityInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BrokersAcitityInformationMessage

/-- Trading Activity By Session Per An Issue Message: 92 bytes -/
structure TradingActivityBySessionPerAnIssueMessage where
  isinCode : Alpha 12
  totalNumberOfTradableIssuesOnCompetitiveTrading : BitVec 32
  premarketAccumulatedTradingVolume : BitVec 64
  premarketAccumulatedTradingValue : Alpha 16
  mainmarketAccumulatedTradingVolume : BitVec 64
  mainmarketAccumulatedTradingValue : Alpha 16
  aftermarketAccumulatedTradingVolume : BitVec 64
  aftermarketAccumulatedTradingValue : Alpha 16
  endKeyword : BitVec 32
  deriving DecidableEq, Repr

namespace TradingActivityBySessionPerAnIssueMessage

def encode (message : TradingActivityBySessionPerAnIssueMessage) : List UInt8 :=
  Alpha.encode message.isinCode
    ++ (encodeUIntLE 4 message.totalNumberOfTradableIssuesOnCompetitiveTrading
    ++ (encodeUIntLE 8 message.premarketAccumulatedTradingVolume
    ++ (Alpha.encode message.premarketAccumulatedTradingValue
    ++ (encodeUIntLE 8 message.mainmarketAccumulatedTradingVolume
    ++ (Alpha.encode message.mainmarketAccumulatedTradingValue
    ++ (encodeUIntLE 8 message.aftermarketAccumulatedTradingVolume
    ++ (Alpha.encode message.aftermarketAccumulatedTradingValue
    ++ (encodeUIntLE 4 message.endKeyword))))))))

def decode (bytes : List UInt8) : Option (TradingActivityBySessionPerAnIssueMessage × List UInt8) := do
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (totalNumberOfTradableIssuesOnCompetitiveTrading, bytes) ← decodeUIntLE 4 bytes
  let (premarketAccumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (premarketAccumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (mainmarketAccumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (mainmarketAccumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (aftermarketAccumulatedTradingVolume, bytes) ← decodeUIntLE 8 bytes
  let (aftermarketAccumulatedTradingValue, bytes) ← Alpha.decode 16 bytes
  let (endKeyword, bytes) ← decodeUIntLE 4 bytes
  pure ({ isinCode, totalNumberOfTradableIssuesOnCompetitiveTrading, premarketAccumulatedTradingVolume, premarketAccumulatedTradingValue, mainmarketAccumulatedTradingVolume, mainmarketAccumulatedTradingValue, aftermarketAccumulatedTradingVolume, aftermarketAccumulatedTradingValue, endKeyword }, bytes)

@[simp] theorem encode_length (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradingActivityBySessionPerAnIssueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActivityBySessionPerAnIssueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingActivityBySessionPerAnIssueMessage

/-- Any Payload, selected by TR Code -/
inductive Payload where
  | pollingDataMessage (message : PollingDataMessage) -- "I2500" 0x4932353030
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage (message : SecuritiesQuoteMmLpQuotesIncluded10LevelMessage) -- "B753S" 0x4237353353
  | securitiesOrderFilledMessage (message : SecuritiesOrderFilledMessage) -- "A353S" 0x4133353353
  | marketOperationTsMessage (message : MarketOperationTsMessage) -- "A753S" 0x4137353353
  | issueClosingMessage (message : IssueClosingMessage) -- "A653S" 0x4136353353
  | triggeringRemovingViMessage (message : TriggeringRemovingViMessage) -- "R853S" 0x5238353353
  | closingPriceTradingQuoteMessage (message : ClosingPriceTradingQuoteMessage) -- "E153S" 0x4531353353
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage (message : EquitiesSnapshotMmLpQuotesIncluded10LevelMessage) -- "B253S" 0x4232353353
  | investorActivitiesPerCommoditiesMessage (message : InvestorActivitiesPerCommoditiesMessage) -- "IC53S" 0x4943353353
  | etpConstituentsMessage (message : EtpConstituentsMessage) -- "V650S" 0x5636353053
  | etpConstituentsMessage297446748243 (message : EtpConstituentsMessage) -- "EA50S" 0x4541353053
  | mmLpInformationMessage (message : MmLpInformationMessage) -- "I753S" 0x4937353353
  | mmLpInformationMessage297463526227 (message : MmLpInformationMessage) -- "EB53S" 0x4542353353
  | marketOperationScheduleMessage (message : MarketOperationScheduleMessage) -- "M453S" 0x4D34353353
  | memberFirmImposingLiftingSanctionsMessage (message : MemberFirmImposingLiftingSanctionsMessage) -- "R350S" 0x5233353053
  | topFiveTradersActivitiesMessage (message : TopFiveTradersActivitiesMessage) -- "B953S" 0x4239353353
  | equitiesBatchDataMessage (message : EquitiesBatchDataMessage) -- "A053S" 0x4130353353
  | equitiesBatchDataMessage297161536339 (message : EquitiesBatchDataMessage) -- "E053S" 0x4530353353
  | memberInformationMessage (message : MemberInformationMessage) -- "M950S" 0x4D39353053
  | memberInformationMessage297295753299 (message : MemberInformationMessage) -- "E850S" 0x4538353053
  | issueEventMessage (message : IssueEventMessage) -- "I653S" 0x4936353353
  | issueEventMessage297262199635 (message : IssueEventMessage) -- "E653S" 0x4536353353
  | blockBasketTradeDataMessage (message : BlockBasketTradeDataMessage) -- "C453S" 0x4334353353
  | investorActivitiesPerAnIssueEodMessage (message : InvestorActivitiesPerAnIssueEodMessage) -- "C153S" 0x4331353353
  | shortSellingMessage (message : ShortSellingMessage) -- "I853S" 0x4938353353
  | brokersAcitityInformationMessage (message : BrokersAcitityInformationMessage) -- "E253S" 0x4532353353
  | tradingActivityBySessionPerAnIssueMessage (message : TradingActivityBySessionPerAnIssueMessage) -- "E353S" 0x4533353353
  deriving DecidableEq, Repr

namespace Payload

/-- The TR Code each message is sent under -/
def tag : Payload → BitVec 40
  | .pollingDataMessage _ => 314374959152
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage _ => 284394074963
  | .securitiesOrderFilledMessage _ => 280031998803
  | .marketOperationTsMessage _ => 280099107667
  | .issueClosingMessage _ => 280082330451
  | .triggeringRemovingViMessage _ => 353130328915
  | .closingPriceTradingQuoteMessage _ => 297178313555
  | .equitiesSnapshotMmLpQuotesIncluded10LevelMessage _ => 284310188883
  | .investorActivitiesPerCommoditiesMessage _ => 314660172627
  | .etpConstituentsMessage _ => 370276642899
  | .etpConstituentsMessage297446748243 _ => 297446748243
  | .mmLpInformationMessage _ => 314458846035
  | .mmLpInformationMessage297463526227 _ => 297463526227
  | .marketOperationScheduleMessage _ => 331588383571
  | .memberFirmImposingLiftingSanctionsMessage _ => 353046442067
  | .topFiveTradersActivitiesMessage _ => 284427629395
  | .equitiesBatchDataMessage _ => 279981667155
  | .equitiesBatchDataMessage297161536339 _ => 297161536339
  | .memberInformationMessage _ => 331672268883
  | .memberInformationMessage297295753299 _ => 297295753299
  | .issueEventMessage _ => 314442068819
  | .issueEventMessage297262199635 _ => 297262199635
  | .blockBasketTradeDataMessage _ => 288638710611
  | .investorActivitiesPerAnIssueEodMessage _ => 288588378963
  | .shortSellingMessage _ => 314475623251
  | .brokersAcitityInformationMessage _ => 297195090771
  | .tradingActivityBySessionPerAnIssueMessage _ => 297211867987

def encode : Payload → List UInt8
  | .pollingDataMessage message => PollingDataMessage.encode message
  | .securitiesQuoteMmLpQuotesIncluded10LevelMessage message => SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode message
  | .securitiesOrderFilledMessage message => SecuritiesOrderFilledMessage.encode message
  | .marketOperationTsMessage message => MarketOperationTsMessage.encode message
  | .issueClosingMessage message => IssueClosingMessage.encode message
  | .triggeringRemovingViMessage message => TriggeringRemovingViMessage.encode message
  | .closingPriceTradingQuoteMessage message => ClosingPriceTradingQuoteMessage.encode message
  | .equitiesSnapshotMmLpQuotesIncluded10LevelMessage message => EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode message
  | .investorActivitiesPerCommoditiesMessage message => InvestorActivitiesPerCommoditiesMessage.encode message
  | .etpConstituentsMessage message => EtpConstituentsMessage.encode message
  | .etpConstituentsMessage297446748243 message => EtpConstituentsMessage.encode message
  | .mmLpInformationMessage message => MmLpInformationMessage.encode message
  | .mmLpInformationMessage297463526227 message => MmLpInformationMessage.encode message
  | .marketOperationScheduleMessage message => MarketOperationScheduleMessage.encode message
  | .memberFirmImposingLiftingSanctionsMessage message => MemberFirmImposingLiftingSanctionsMessage.encode message
  | .topFiveTradersActivitiesMessage message => TopFiveTradersActivitiesMessage.encode message
  | .equitiesBatchDataMessage message => EquitiesBatchDataMessage.encode message
  | .equitiesBatchDataMessage297161536339 message => EquitiesBatchDataMessage.encode message
  | .memberInformationMessage message => MemberInformationMessage.encode message
  | .memberInformationMessage297295753299 message => MemberInformationMessage.encode message
  | .issueEventMessage message => IssueEventMessage.encode message
  | .issueEventMessage297262199635 message => IssueEventMessage.encode message
  | .blockBasketTradeDataMessage message => BlockBasketTradeDataMessage.encode message
  | .investorActivitiesPerAnIssueEodMessage message => InvestorActivitiesPerAnIssueEodMessage.encode message
  | .shortSellingMessage message => ShortSellingMessage.encode message
  | .brokersAcitityInformationMessage message => BrokersAcitityInformationMessage.encode message
  | .tradingActivityBySessionPerAnIssueMessage message => TradingActivityBySessionPerAnIssueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 654 := by
  cases message with
  | pollingDataMessage inner =>
    simp only [encode, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [encode, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [encode, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [encode, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [encode, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [encode, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [encode, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage inner =>
    simp only [encode, EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | investorActivitiesPerCommoditiesMessage inner =>
    simp only [encode, InvestorActivitiesPerCommoditiesMessage.encode_length]
    omega
  | etpConstituentsMessage inner =>
    simp only [encode, EtpConstituentsMessage.encode_length]
    omega
  | etpConstituentsMessage297446748243 inner =>
    simp only [encode, EtpConstituentsMessage.encode_length]
    omega
  | mmLpInformationMessage inner =>
    simp only [encode, MmLpInformationMessage.encode_length]
    omega
  | mmLpInformationMessage297463526227 inner =>
    simp only [encode, MmLpInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [encode, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [encode, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [encode, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161536339 inner =>
    simp only [encode, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753299 inner =>
    simp only [encode, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199635 inner =>
    simp only [encode, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [encode, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [encode, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [encode, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [encode, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [encode, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 314374959152 then (PollingDataMessage.decode bytes).map fun (message, rest) => (.pollingDataMessage message, rest)
  else if tag = 284394074963 then (SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.decode bytes).map fun (message, rest) => (.securitiesQuoteMmLpQuotesIncluded10LevelMessage message, rest)
  else if tag = 280031998803 then (SecuritiesOrderFilledMessage.decode bytes).map fun (message, rest) => (.securitiesOrderFilledMessage message, rest)
  else if tag = 280099107667 then (MarketOperationTsMessage.decode bytes).map fun (message, rest) => (.marketOperationTsMessage message, rest)
  else if tag = 280082330451 then (IssueClosingMessage.decode bytes).map fun (message, rest) => (.issueClosingMessage message, rest)
  else if tag = 353130328915 then (TriggeringRemovingViMessage.decode bytes).map fun (message, rest) => (.triggeringRemovingViMessage message, rest)
  else if tag = 297178313555 then (ClosingPriceTradingQuoteMessage.decode bytes).map fun (message, rest) => (.closingPriceTradingQuoteMessage message, rest)
  else if tag = 284310188883 then (EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.decode bytes).map fun (message, rest) => (.equitiesSnapshotMmLpQuotesIncluded10LevelMessage message, rest)
  else if tag = 314660172627 then (InvestorActivitiesPerCommoditiesMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerCommoditiesMessage message, rest)
  else if tag = 370276642899 then (EtpConstituentsMessage.decode bytes).map fun (message, rest) => (.etpConstituentsMessage message, rest)
  else if tag = 297446748243 then (EtpConstituentsMessage.decode bytes).map fun (message, rest) => (.etpConstituentsMessage297446748243 message, rest)
  else if tag = 314458846035 then (MmLpInformationMessage.decode bytes).map fun (message, rest) => (.mmLpInformationMessage message, rest)
  else if tag = 297463526227 then (MmLpInformationMessage.decode bytes).map fun (message, rest) => (.mmLpInformationMessage297463526227 message, rest)
  else if tag = 331588383571 then (MarketOperationScheduleMessage.decode bytes).map fun (message, rest) => (.marketOperationScheduleMessage message, rest)
  else if tag = 353046442067 then (MemberFirmImposingLiftingSanctionsMessage.decode bytes).map fun (message, rest) => (.memberFirmImposingLiftingSanctionsMessage message, rest)
  else if tag = 284427629395 then (TopFiveTradersActivitiesMessage.decode bytes).map fun (message, rest) => (.topFiveTradersActivitiesMessage message, rest)
  else if tag = 279981667155 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage message, rest)
  else if tag = 297161536339 then (EquitiesBatchDataMessage.decode bytes).map fun (message, rest) => (.equitiesBatchDataMessage297161536339 message, rest)
  else if tag = 331672268883 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage message, rest)
  else if tag = 297295753299 then (MemberInformationMessage.decode bytes).map fun (message, rest) => (.memberInformationMessage297295753299 message, rest)
  else if tag = 314442068819 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage message, rest)
  else if tag = 297262199635 then (IssueEventMessage.decode bytes).map fun (message, rest) => (.issueEventMessage297262199635 message, rest)
  else if tag = 288638710611 then (BlockBasketTradeDataMessage.decode bytes).map fun (message, rest) => (.blockBasketTradeDataMessage message, rest)
  else if tag = 288588378963 then (InvestorActivitiesPerAnIssueEodMessage.decode bytes).map fun (message, rest) => (.investorActivitiesPerAnIssueEodMessage message, rest)
  else if tag = 314475623251 then (ShortSellingMessage.decode bytes).map fun (message, rest) => (.shortSellingMessage message, rest)
  else if tag = 297195090771 then (BrokersAcitityInformationMessage.decode bytes).map fun (message, rest) => (.brokersAcitityInformationMessage message, rest)
  else if tag = 297211867987 then (TradingActivityBySessionPerAnIssueMessage.decode bytes).map fun (message, rest) => (.tradingActivityBySessionPerAnIssueMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 5 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (trCode, bytes) ← decodeUInt 5 bytes
  let (payload, bytes) ← Payload.decode trCode bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 659 := by
  unfold encode
  cases message.payload with
  | pollingDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PollingDataMessage.encode_length]
    omega
  | securitiesQuoteMmLpQuotesIncluded10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | securitiesOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecuritiesOrderFilledMessage.encode_length]
    omega
  | marketOperationTsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationTsMessage.encode_length]
    omega
  | issueClosingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueClosingMessage.encode_length]
    omega
  | triggeringRemovingViMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TriggeringRemovingViMessage.encode_length]
    omega
  | closingPriceTradingQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceTradingQuoteMessage.encode_length]
    omega
  | equitiesSnapshotMmLpQuotesIncluded10LevelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.encode_length]
    omega
  | investorActivitiesPerCommoditiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerCommoditiesMessage.encode_length]
    omega
  | etpConstituentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EtpConstituentsMessage.encode_length]
    omega
  | etpConstituentsMessage297446748243 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EtpConstituentsMessage.encode_length]
    omega
  | mmLpInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MmLpInformationMessage.encode_length]
    omega
  | mmLpInformationMessage297463526227 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MmLpInformationMessage.encode_length]
    omega
  | marketOperationScheduleMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketOperationScheduleMessage.encode_length]
    omega
  | memberFirmImposingLiftingSanctionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberFirmImposingLiftingSanctionsMessage.encode_length]
    omega
  | topFiveTradersActivitiesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopFiveTradersActivitiesMessage.encode_length]
    omega
  | equitiesBatchDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | equitiesBatchDataMessage297161536339 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesBatchDataMessage.encode_length]
    omega
  | memberInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | memberInformationMessage297295753299 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MemberInformationMessage.encode_length]
    omega
  | issueEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | issueEventMessage297262199635 inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IssueEventMessage.encode_length]
    omega
  | blockBasketTradeDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BlockBasketTradeDataMessage.encode_length]
    omega
  | investorActivitiesPerAnIssueEodMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InvestorActivitiesPerAnIssueEodMessage.encode_length]
    omega
  | shortSellingMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSellingMessage.encode_length]
    omega
  | brokersAcitityInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokersAcitityInformationMessage.encode_length]
    omega
  | tradingActivityBySessionPerAnIssueMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActivityBySessionPerAnIssueMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Packet

end Omi.NextradeNextradeEtpcommonNxtbinaryV212
