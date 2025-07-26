package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"runtime/pprof"


	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/dgraph-io/badger/v3"
	"github.com/pkg/profile"
)

func main() {
	// go func() {
    //     log.Println(http.ListenAndServe("localhost:6060", nil))
    // }()

	// 创建CPU profiling文件
    f, err := os.Create("cpu.prof")
    if err != nil {
        log.Fatal("could not create CPU profile: ", err)
    }
    defer f.Close()

    // 启动CPU profiling
    if err := pprof.StartCPUProfile(f); err != nil {
        log.Fatal("could not start CPU profile: ", err)
    }
    defer pprof.StopCPUProfile()

    // 创建一个通道来接收信号
    cc := make(chan os.Signal, 1)
    // 监听SIGINT（Ctrl+C）和SIGTERM信号
    signal.Notify(cc, os.Interrupt, syscall.SIGTERM)

    // 启动一个goroutine来处理信号
    go func() {
        // 等待信号
        sig := <-cc
        log.Printf("Received signal: %s", sig)

        // 停止CPU profiling
        pprof.StopCPUProfile()
        log.Println("CPU profiling stopped")

        // 确保文件已关闭
        f.Close()
        log.Println("CPU profile file closed")

        // 退出程序
        os.Exit(1)
    }()
	
	var srvId int
	var configPath string
	var profileMode string
	flag.IntVar(&srvId, "srvId", -1, "Server ID")
	flag.StringVar(&configPath, "c", "", "Config file")
	flag.StringVar(&profileMode, "profile.mode", "", "enable profiling mode, one of [cpu, mem, mutex, block, goroutine, trace]")

	flag.Parse()

	if srvId == -1 {
		log.Fatal("srvId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}
	if profileMode != "" {
		profilePath := filepath.Join("profiles", fmt.Sprintf("srv%d", srvId))

		switch profileMode {
		case "cpu":
			defer profile.Start(profile.CPUProfile, profile.ProfilePath(profilePath)).Stop()
		case "mem":
			defer profile.Start(profile.MemProfile, profile.ProfilePath(profilePath)).Stop()
		case "mutex":
			defer profile.Start(profile.MutexProfile, profile.ProfilePath(profilePath)).Stop()
		case "block":
			defer profile.Start(profile.BlockProfile, profile.ProfilePath(profilePath)).Stop()
		case "goroutine":
			defer profile.Start(profile.GoroutineProfile, profile.ProfilePath(profilePath)).Stop()
		case "trace":
			defer profile.Start(profile.TraceProfile, profile.ProfilePath(profilePath)).Stop()
		default:
			log.Fatal("invalid profile.mode value")
		}
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	dbPath := fmt.Sprintf("/tmp/raftkvs/server%d/badger", srvId)

	// temp: removing existing badger files
	log.Println("removing badger files")
	if err := os.RemoveAll(dbPath); err != nil {
		log.Println(err)
	}

	log.Println("persist", c.Persist)

	var db *badger.DB
	if c.Persist {
		db, err = badger.Open(badger.DefaultOptions(dbPath))
		if err != nil {
			log.Fatal(err)
		}
		defer func() {
			if err := db.Close(); err != nil {
				log.Println(err)
			}
		}()
	}

	s := bootstrap.NewServer(srvId, c, db)

	go func() {
		err := s.Run()
		if err != nil {
			log.Println(err)
		}
	}()

	defer func() {
		err := s.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

	<-sigCh
	log.Println("received SIGTERM")
}
