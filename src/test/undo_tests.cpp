// Copyright (c) 2017 Amaury SÉCHET
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "undo.h"
#include "chainparams.h"
#include "consensus/validation.h"
#include "validation.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(undo_tests, BasicTestingSetup)

// 将块中的交易应用在UTXO集合中，并更新UTXO集合，返回块的 undo信息。
static void UpdateUTXOSet(const CBlock &block, CCoinsViewCache &view,
                          CBlockUndo &blockundo,
                          const CChainParams &chainparams, uint32_t nHeight) {
    CValidationState state;

    auto &coinbaseTx = *block.vtx[0];
    //1. 先向UTXO集合中，更新coinbase交易，这个coinbase交易没有undo信息。
    UpdateCoins(coinbaseTx, view, nHeight);

    //2. 再向UTXO集合中更新块的其他交易，返回这些交易的undo信息
    for (size_t i = 1; i < block.vtx.size(); i++) {
        auto &tx = *block.vtx[1];

        blockundo.vtxundo.push_back(CTxUndo());
        UpdateCoins(tx, view, blockundo.vtxundo.back(), nHeight);
    }

    //3. 设置这个块为当前UTXO集合的最新块。
    view.SetBestBlock(block.GetHash());
}

// block(in):将要被撤销的块。 view(in/out): UTXO集合。
// blockundo(in): 该撤销块对应的undo信息
static void UndoBlock(const CBlock &block, CCoinsViewCache &view,
                      const CBlockUndo &blockUndo,
                      const CChainParams &chainparams, uint32_t nHeight) {
    CBlockIndex pindex;
    pindex.nHeight = nHeight;
    //应用block的 undo信息至UTXO集合中
    ApplyBlockUndo(blockUndo, block, &pindex, view);
}

static bool HasSpendableCoin(const CCoinsViewCache &view, const uint256 &txid) {
    return !view.AccessCoin(COutPoint(txid, 0)).IsSpent();
}

BOOST_AUTO_TEST_CASE(connect_utxo_extblock) {
    //选择链参数
    SelectParams(CBaseChainParams::MAIN);
    const CChainParams &chainparams = Params();

    CBlock block;
    CMutableTransaction tx;

    // 实际存储UTXO的 对象。
    CCoinsView coinsDummy;
    CCoinsViewCache view(&coinsDummy);

    // 该块 height = 1；
    block.hashPrevBlock = GetRandHash();        //此处为创世块的哈希
    view.SetBestBlock(block.hashPrevBlock);

    // Create a block with coinbase and resolution transaction.
    // 创建一个coinbase交易和决议交易
    // 一个交易输入，没有引用输出，只有签名脚本字段的数据。 一个交易输出；
    // coinbase 交易， 构造coinbase交易，并获取它的交易ID。
    tx.vin.resize(1);
    tx.vin[0].scriptSig.resize(10);
    tx.vout.resize(1);
    tx.vout[0].nValue = 42;
    auto coinbaseTx = CTransaction(tx);

    // 该块中存储2个交易，
    block.vtx.resize(2);
    // 第一个为coinbase交易
    block.vtx[0] = MakeTransactionRef(tx);

    // 修改该交易的交易输入字段； 对上述已存入的交易无影响。
    tx.vout[0].scriptPubKey = CScript() << OP_TRUE;
    tx.vin[0].prevout.hash = GetRandHash();
    tx.vin[0].prevout.n = 0;
    tx.vin[0].nSequence = CTxIn::SEQUENCE_FINAL;
    tx.vin[0].scriptSig.resize(0);
    tx.nVersion = 2;

    auto prevTx0 = CTransaction(tx);
    // 为当前添加交易的每个输出 构造UTXO，并将它们添加进UTXO集合中。
    AddCoins(view, prevTx0, 100);

    // 将上一步加入到UTXO的交易花掉；并将这个交易打包进block中
    tx.vin[0].prevout.hash = prevTx0.GetId();
    auto tx0 = CTransaction(tx);
    block.vtx[1] = MakeTransactionRef(tx0);

    // Now update the UTXO set.
    CBlockUndo blockundo;
    // 依据块中的交易，去更新UTXO集合。此时prevTx0 将不可以花费
    UpdateUTXOSet(block, view, blockundo, chainparams, 123456);

    BOOST_CHECK(view.GetBestBlock() == block.GetHash());
    BOOST_CHECK(HasSpendableCoin(view, coinbaseTx.GetId()));
    BOOST_CHECK(HasSpendableCoin(view, tx0.GetId()));
    BOOST_CHECK(!HasSpendableCoin(view, prevTx0.GetId()));

    // 应用undo文件; 撤销这个块中的引用输出交易
    UndoBlock(block, view, blockundo, chainparams, 123456);

    BOOST_CHECK(view.GetBestBlock() == block.hashPrevBlock);
    BOOST_CHECK(!HasSpendableCoin(view, coinbaseTx.GetId()));
    BOOST_CHECK(!HasSpendableCoin(view, tx0.GetId()));
    BOOST_CHECK(HasSpendableCoin(view, prevTx0.GetId()));
}

BOOST_AUTO_TEST_SUITE_END()
