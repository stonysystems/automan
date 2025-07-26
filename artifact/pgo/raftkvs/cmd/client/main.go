package main

import (
	"errors"
	"flag"
	"fmt"
	"log"
	"strings"
	"time"
	"strconv"
	"sync"
	"os"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
)

var ErrInvalidCmd = errors.New("invalid command")

func parseCmd(cmd string) (bootstrap.Request, error) {
	words := strings.Split(cmd, " ")
	if len(words) < 1 {
		return nil, ErrInvalidCmd
	}

	reqType := words[0]
	switch strings.ToLower(reqType) {
	case "get":
		if len(words) < 2 {
			return nil, ErrInvalidCmd
		}
		return bootstrap.GetRequest{
			Key: words[1],
		}, nil
	case "put":
		if len(words) < 2 {
			return nil, ErrInvalidCmd
		}
		return bootstrap.PutRequest{
			Key:   words[1],
			Value: words[2],
		}, nil
	default:
		return nil, ErrInvalidCmd
	}
}

func printResp(resp bootstrap.Response) {
	if !resp.OK {
		fmt.Println("key not found")
	} else {
		fmt.Printf("%v %v\n", resp.Key, resp.Value)
	}
}

func main() {
	var clientId int
	var configPath string
	flag.IntVar(&clientId, "clientId", -1, "Client ID")
	flag.StringVar(&configPath, "c", "", "Config file")

	flag.Parse()

	if clientId == -1 {
		log.Fatal("clientId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	client := bootstrap.NewClient(clientId, c)

	reqCh := make(chan bootstrap.Request)
	respCh := make(chan bootstrap.Response)
	go func() {
		err := client.Run(reqCh, respCh)
		if err != nil {
			log.Println(err)
		}
	}()

	defer func() {
		close(reqCh)
		close(respCh)
		err := client.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	// scanner := bufio.NewScanner(os.Stdin)

	startTime := time.Now()
	duration := 30 * time.Second 
	endTime := startTime.Add(duration)
	totalRequests := 0
	var totalLatency time.Duration
	var mu sync.Mutex
	var wg sync.WaitGroup
	numThreads := 1

	for i := 0; i < numThreads; i++ {
		wg.Add(1)
		go func(threadId int) {
			defer wg.Done()
			localRequests := 0
			var localLatency time.Duration

			for time.Now().Before(endTime) {
				key := threadId*1000000 + localRequests
				value := threadId*1000000 + localRequests

				req := bootstrap.PutRequest{
					Key:   strconv.Itoa(key),
					Value: strconv.Itoa(value),
				}

				startOpTime := time.Now()
				reqCh <- req
				resp := <-respCh
				endOpTime := time.Now()

				if resp.OK {
					localRequests++
					localLatency += endOpTime.Sub(startOpTime)
				}
			}

			// fmt.Printf("Local put operations: %d\n", localRequests)

			mu.Lock()
			totalRequests += localRequests
			totalLatency += localLatency
			mu.Unlock()
		}(i)
		// for time.Now().Before(endTime) {
		// 	key := totalRequests
		// 	value := totalRequests

		// 	req := bootstrap.PutRequest{
		// 		Key:   strconv.Itoa(key),
		// 		Value: strconv.Itoa(value),
		// 	}

		// 	startOpTime := time.Now()
		// 	reqCh <- req
		// 	resp := <-respCh
		// 	endOpTime := time.Now()

		// 	if resp.OK{
		// 		totalRequests++
		// 		totalLatency += endOpTime.Sub(startOpTime)
		// 	}
		// }
	}

	wg.Wait()

	throughput := float64(totalRequests) / duration.Seconds()
	averageLatency := totalLatency / time.Duration(totalRequests)

	result := fmt.Sprintf("throughput: %.2f, latency: %s\n", throughput, averageLatency)

	fmt.Print(result)

	f, err := os.OpenFile("experiment_result.txt", os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fmt.Printf("error opening result file: %v\n", err)
		return
	}
	defer f.Close()

	if _, err := f.WriteString(result); err != nil {
		fmt.Printf("error writing result: %v\n", err)
	}

}
