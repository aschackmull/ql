// Code generated by depstubber. DO NOT EDIT.
// This is a simple stub for github.com/go-pg/pg/v10, strictly for use in testing.

// See the LICENSE file for information about the licensing of the original library.
// Source: github.com/go-pg/pg/v10 (exports: DB; functions: Connect,Scan)

// Package pg is a stub of github.com/go-pg/pg/v10, generated by depstubber.
package pg

import (
	context "context"
	tls "crypto/tls"
	io "io"
	net "net"
	time "time"
  orm "github.com/go-pg/pg/v10/orm"
)

type Conn struct{}

func (_ Conn) AddQueryHook(_ QueryHook) {}

func (_ Conn) Begin() (*Tx, error) {
	return nil, nil
}

func (_ Conn) BeginContext(_ context.Context) (*Tx, error) {
	return nil, nil
}

func (_ Conn) Close() error {
	return nil
}

func (_ Conn) CopyFrom(_ io.Reader, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) CopyTo(_ io.Writer, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) Exec(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) ExecContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) ExecOne(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) ExecOneContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) Formatter() interface{} {
	return nil
}

func (_ Conn) Model(_ ...interface{}) *orm.Query {
	return new(orm.Query)
}

func (_ Conn) ModelContext(_ context.Context, _ ...interface{}) interface{} {
	return nil
}

func (_ Conn) Param(_ string) interface{} {
	return nil
}

func (_ Conn) Ping(_ context.Context) error {
	return nil
}

func (_ Conn) PoolStats() *PoolStats {
	return nil
}

func (_ Conn) Prepare(_ string) (*Stmt, error) {
	return nil, nil
}

func (_ Conn) Query(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) QueryContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) QueryOne(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) QueryOneContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ Conn) RunInTransaction(_ context.Context, _ func(*Tx) error) error {
	return nil
}

func (_ *Conn) Context() context.Context {
	return nil
}

func (_ *Conn) WithContext(_ context.Context) *Conn {
	return nil
}

func (_ *Conn) WithParam(_ string, _ interface{}) *Conn {
	return nil
}

func (_ *Conn) WithTimeout(_ time.Duration) *Conn {
	return nil
}

func Connect(_ *Options) *DB {
	return nil
}

type DB struct{}

func (_ DB) AddQueryHook(_ QueryHook) {}

func (_ DB) Begin() (*Tx, error) {
	return nil, nil
}

func (_ DB) BeginContext(_ context.Context) (*Tx, error) {
	return nil, nil
}

func (_ DB) Close() error {
	return nil
}

func (_ DB) CopyFrom(_ io.Reader, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) CopyTo(_ io.Writer, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) Exec(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) ExecContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) ExecOne(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) ExecOneContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) Formatter() interface{} {
	return nil
}

func (_ DB) Model(_ ...interface{}) *orm.Query {
	return new(orm.Query)
}

func (_ DB) ModelContext(_ context.Context, _ ...interface{}) interface{} {
	return nil
}

func (_ DB) Param(_ string) interface{} {
	return nil
}

func (_ DB) Ping(_ context.Context) error {
	return nil
}

func (_ DB) PoolStats() *PoolStats {
	return nil
}

func (_ DB) Prepare(_ string) (*Stmt, error) {
	return nil, nil
}

func (_ DB) Query(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) QueryContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) QueryOne(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) QueryOneContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ DB) RunInTransaction(_ context.Context, _ func(*Tx) error) error {
	return nil
}

func (_ *DB) Conn() *Conn {
	return nil
}

func (_ *DB) Context() context.Context {
	return nil
}

func (_ *DB) Listen(_ context.Context, _ ...string) *Listener {
	return nil
}

func (_ *DB) Options() *Options {
	return nil
}

func (_ *DB) String() string {
	return ""
}

func (_ *DB) WithContext(_ context.Context) *DB {
	return nil
}

func (_ *DB) WithParam(_ string, _ interface{}) *DB {
	return nil
}

func (_ *DB) WithTimeout(_ time.Duration) *DB {
	return nil
}

type Listener struct{}

func (_ *Listener) Channel() <-chan Notification {
	return nil
}

func (_ *Listener) ChannelSize(_ int) <-chan Notification {
	return nil
}

func (_ *Listener) Close() error {
	return nil
}

func (_ *Listener) Listen(_ context.Context, _ ...string) error {
	return nil
}

func (_ *Listener) Receive(_ context.Context) (string, string, error) {
	return "", "", nil
}

func (_ *Listener) ReceiveTimeout(_ context.Context, _ time.Duration) (string, string, error) {
	return "", "", nil
}

func (_ *Listener) String() string {
	return ""
}

func (_ *Listener) Unlisten(_ context.Context, _ ...string) error {
	return nil
}

type Notification struct {
	Channel string
	Payload string
}

type Options struct {
	Network               string
	Addr                  string
	Dialer                func(context.Context, string, string) (net.Conn, error)
	OnConnect             func(context.Context, *Conn) error
	User                  string
	Password              string
	Database              string
	ApplicationName       string
	TLSConfig             *tls.Config
	DialTimeout           time.Duration
	ReadTimeout           time.Duration
	WriteTimeout          time.Duration
	MaxRetries            int
	RetryStatementTimeout bool
	MinRetryBackoff       time.Duration
	MaxRetryBackoff       time.Duration
	PoolSize              int
	MinIdleConns          int
	MaxConnAge            time.Duration
	PoolTimeout           time.Duration
	IdleTimeout           time.Duration
	IdleCheckFrequency    time.Duration
}

type PoolStats struct {
	Hits       uint32
	Misses     uint32
	Timeouts   uint32
	TotalConns uint32
	IdleConns  uint32
	StaleConns uint32
}

type QueryEvent struct {
	StartTime time.Time
	DB        interface{}
	Model     interface{}
	Query     interface{}
	Params    []interface{}
	Result    interface{}
	Err       error
	Stash     map[interface{}]interface{}
}

func (_ *QueryEvent) FormattedQuery() ([]byte, error) {
	return nil, nil
}

func (_ *QueryEvent) UnformattedQuery() ([]byte, error) {
	return nil, nil
}

type QueryHook interface {
	AfterQuery(_ context.Context, _ *QueryEvent) error
	BeforeQuery(_ context.Context, _ *QueryEvent) (context.Context, error)
}

func Scan(_ ...interface{}) interface{} {
	return nil
}

type Stmt struct{}

func (_ *Stmt) Close() error {
	return nil
}

func (_ *Stmt) Exec(_ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) ExecContext(_ context.Context, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) ExecOne(_ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) ExecOneContext(_ context.Context, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) Query(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) QueryContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) QueryOne(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Stmt) QueryOneContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

type Tx struct{}

func (_ *Tx) Begin() (*Tx, error) {
	return nil, nil
}

func (_ *Tx) Close() error {
	return nil
}

func (_ *Tx) CloseContext(_ context.Context) error {
	return nil
}

func (_ *Tx) Commit() error {
	return nil
}

func (_ *Tx) CommitContext(_ context.Context) error {
	return nil
}

func (_ *Tx) Context() context.Context {
	return nil
}

func (_ *Tx) CopyFrom(_ io.Reader, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) CopyTo(_ io.Writer, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) Exec(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) ExecContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) ExecOne(_ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) ExecOneContext(_ context.Context, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) Formatter() interface{} {
	return nil
}

func (_ *Tx) Model(_ ...interface{}) interface{} {
	return nil
}

func (_ *Tx) ModelContext(_ context.Context, _ ...interface{}) interface{} {
	return nil
}

func (_ *Tx) Prepare(_ string) (*Stmt, error) {
	return nil, nil
}

func (_ *Tx) Query(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) QueryContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) QueryOne(_ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) QueryOneContext(_ context.Context, _ interface{}, _ interface{}, _ ...interface{}) (interface{}, error) {
	return nil, nil
}

func (_ *Tx) Rollback() error {
	return nil
}

func (_ *Tx) RollbackContext(_ context.Context) error {
	return nil
}

func (_ *Tx) RunInTransaction(_ context.Context, _ func(*Tx) error) error {
	return nil
}

func (_ *Tx) Stmt(_ *Stmt) *Stmt {
	return nil
}
