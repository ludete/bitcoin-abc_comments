// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#if defined(HAVE_CONFIG_H)
#include "config/bitcoin-config.h"
#endif

#include "chainparams.h"
#include "clientversion.h"
#include "compat.h"
#include "config.h"
#include "httprpc.h"
#include "httpserver.h"
#include "init.h"
#include "noui.h"
#include "rpc/server.h"
#include "scheduler.h"
#include "util.h"
#include "utilstrencodings.h"

#include <boost/algorithm/string/predicate.hpp>
#include <boost/filesystem.hpp>
#include <boost/thread.hpp>

#include <cstdio>

/* Introduction text for doxygen: */

/*! \mainpage Developer documentation
 *
 * \section intro_sec Introduction
 *
 * This is the developer documentation of the reference client for an
 * experimental new digital currency called Bitcoin (https://www.bitcoin.org/),
 * which enables instant payments to anyone, anywhere in the world. Bitcoin uses
 * peer-to-peer technology to operate with no central authority: managing
 * transactions and issuing money are carried out collectively by the network.
 *
 * The software is a community-driven open source project, released under the
 * MIT license.
 *
 * \section Navigation
 * Use the buttons <code>Namespaces</code>, <code>Classes</code> or
 * <code>Files</code> at the top of the page to start navigating the code.
 */

void WaitForShutdown(boost::thread_group *threadGroup) {
    bool fShutdown = ShutdownRequested();
    // Tell the main threads to shutdown.
    while (!fShutdown) {
        MilliSleep(200);
        fShutdown = ShutdownRequested();
    }
    if (threadGroup) {
        Interrupt(*threadGroup);
        threadGroup->join_all();
    }
}

//////////////////////////////////////////////////////////////////////////////
//
// Start
// 开始启动APP
bool AppInit(int argc, char *argv[]) {
    boost::thread_group threadGroup;
    CScheduler scheduler;

    // FIXME: Ideally, we'd like to build the config here, but that's currently
    // not possible as the whole application has too many global state. However,
    // this is a first step.
    auto &config = const_cast<Config &>(GetConfig());

    bool fRet = false;

    //
    // Parameters
    //
    // If Qt is used, parameters/bitcoin.conf are parsed in qt/bitcoin.cpp's
    // main()
    // 解析命令行参数；放到全局变量，以便后来使用
    ParseParameters(argc, argv);

    // Process help and version before taking care about datadir
    // 返回使用查看帮助信息 或 版本信息
    if (IsArgSet("-?") || IsArgSet("-h") || IsArgSet("-help") ||
        IsArgSet("-version")) {
        std::string strUsage = strprintf(_("%s Daemon"), _(PACKAGE_NAME)) +
                               " " + _("version") + " " + FormatFullVersion() +
                               "\n";

        if (IsArgSet("-version")) {
            strUsage += FormatParagraph(LicenseInfo());
        } else {
            strUsage += "\n" + _("Usage:") + "\n" +
                        "  bitcoind [options]                     " +
                        strprintf(_("Start %s Daemon"), _(PACKAGE_NAME)) + "\n";

            strUsage += "\n" + HelpMessage(HMM_BITCOIND);
        }

        fprintf(stdout, "%s", strUsage.c_str());
        return true;
    }

    try {
        // 查看传入的目录是否存在；
        if (!boost::filesystem::is_directory(GetDataDir(false))) {
            fprintf(stderr,
                    "Error: Specified data directory \"%s\" does not exist.\n",
                    GetArg("-datadir", "").c_str());
            return false;
        }
        try {
            // 读取配置文件
            ReadConfigFile(GetArg("-conf", BITCOIN_CONF_FILENAME));
        } catch (const std::exception &e) {
            fprintf(stderr, "Error reading configuration file: %s\n", e.what());
            return false;
        }
        // Check for -testnet or -regtest parameter (Params() calls are only
        // valid after this clause)
        try {
            // 选择当前运行的块链(主链，侧链，回归测试链)
            SelectParams(ChainNameFromCommandLine());
        } catch (const std::exception &e) {
            fprintf(stderr, "Error: %s\n", e.what());
            return false;
        }

        // Command-line RPC 命令行RPC
        bool fCommandLine = false;
        for (int i = 1; i < argc; i++)
            if (!IsSwitchChar(argv[i][0]) &&
                !boost::algorithm::istarts_with(argv[i], "bitcoin:"))
                fCommandLine = true;

        if (fCommandLine) {
            fprintf(stderr, "Error: There is no RPC client functionality in "
                            "bitcoind anymore. Use the bitcoin-cli utility "
                            "instead.\n");
            exit(EXIT_FAILURE);
        }
        // -server defaults to true for bitcoind but not for the GUI so do this
        // here 向全局的命令行缓存中写入 -server 配置
        SoftSetBoolArg("-server", true);
        // Set this early so that parameter interactions go to console
        // 尽早设置log，以便参数交互进入控制台
        InitLogging();
        InitParameterInteraction();
        // 设置系统信号
        if (!AppInitBasicSetup()) {
            // InitError will have been called with detailed error, which ends
            // up on console
            exit(1);
        }
        // 设置软件的运行参数
        if (!AppInitParameterInteraction(config)) {
            // InitError will have been called with detailed error, which ends
            // up on console
            exit(1);
        }
        // 进行合理性的检查；
        if (!AppInitSanityChecks()) {
            // InitError will have been called with detailed error, which ends
            // up on console
            exit(1);
        }
        if (GetBoolArg("-daemon", false)) {
#if HAVE_DECL_DAEMON
            fprintf(stdout, "Bitcoin server starting\n");

            // Daemonize
            if (daemon(1, 0)) {
                // don't chdir (1), do close FDs (0)
                fprintf(stderr, "Error: daemon() failed: %s\n",
                        strerror(errno));
                return false;
            }
#else
            fprintf(
                stderr,
                "Error: -daemon is not supported on this operating system\n");
            return false;
#endif // HAVE_DECL_DAEMON
        }
        // 进行程序启动
        fRet = AppInitMain(config, threadGroup, scheduler);
    } catch (const std::exception &e) {
        PrintExceptionContinue(&e, "AppInit()");
    } catch (...) {
        PrintExceptionContinue(nullptr, "AppInit()");
    }

    if (!fRet) {
        Interrupt(threadGroup);
        // threadGroup.join_all(); was left out intentionally here, because we
        // didn't re-test all of the startup-failure cases to make sure they
        // don't result in a hang due to some
        // thread-blocking-waiting-for-another-thread-during-startup case.
    } else {
        WaitForShutdown(&threadGroup);/
    }
    Shutdown();

    return fRet;
}

int main(int argc, char *argv[]) {
    SetupEnvironment();

    // Connect bitcoind signal handlers
    noui_connect();

    return (AppInit(argc, argv) ? EXIT_SUCCESS : EXIT_FAILURE);
}
