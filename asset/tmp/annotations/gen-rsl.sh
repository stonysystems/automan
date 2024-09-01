#!/bin/bash

find Common/*.automan RSL/*.automan -exec cat {} \; -exec echo \; > RSL.automan
