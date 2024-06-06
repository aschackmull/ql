// Code generated by depstubber. DO NOT EDIT.
// This is a simple stub for github.com/gin-gonic/gin, strictly for use in testing.

// See the LICENSE file for information about the licensing of the original library.
// Source: github.com/gin-gonic/gin (exports: Context; functions: Default)

// Package gin is a stub of github.com/gin-gonic/gin, generated by depstubber.
package gin

import (
	bufio "bufio"
	template "html/template"
	io "io"
	multipart "mime/multipart"
	net "net"
	http "net/http"
	sync "sync"
	template0 "text/template"
	time "time"
)

type Context struct {
	Request   *http.Request
	Writer    ResponseWriter
	Params    Params
	KeysMutex *sync.RWMutex
	Keys      map[string]interface{}
	Errors    interface{}
	Accepted  []string
}

func (_ *Context) Abort() {}

func (_ *Context) AbortWithError(_ int, _ error) *Error {
	return nil
}

func (_ *Context) AbortWithStatus(_ int) {}

func (_ *Context) AbortWithStatusJSON(_ int, _ interface{}) {}

func (_ *Context) AsciiJSON(_ int, _ interface{}) {}

func (_ *Context) Bind(_ interface{}) error {
	return nil
}

func (_ *Context) BindHeader(_ interface{}) error {
	return nil
}

func (_ *Context) BindJSON(_ interface{}) error {
	return nil
}

func (_ *Context) BindQuery(_ interface{}) error {
	return nil
}

func (_ *Context) BindUri(_ interface{}) error {
	return nil
}

func (_ *Context) BindWith(_ interface{}, _ interface{}) error {
	return nil
}

func (_ *Context) BindXML(_ interface{}) error {
	return nil
}

func (_ *Context) BindYAML(_ interface{}) error {
	return nil
}

func (_ *Context) ClientIP() string {
	return ""
}

func (_ *Context) ContentType() string {
	return ""
}

func (_ *Context) Cookie(_ string) (string, error) {
	return "", nil
}

func (_ *Context) Copy() *Context {
	return nil
}

func (_ *Context) Data(_ int, _ string, _ []byte) {}

func (_ *Context) DataFromReader(_ int, _ int64, _ string, _ io.Reader, _ map[string]string) {}

func (_ *Context) Deadline() (time.Time, bool) {
	return time.Time{}, false
}

func (_ *Context) DefaultPostForm(_ string, _ string) string {
	return ""
}

func (_ *Context) DefaultQuery(_ string, _ string) string {
	return ""
}

func (_ *Context) Done() <-chan struct{} {
	return nil
}

func (_ *Context) Err() error {
	return nil
}

func (_ *Context) Error(_ error) *Error {
	return nil
}

func (_ *Context) File(_ string) {}

func (_ *Context) FileAttachment(_ string, _ string) {}

func (_ *Context) FileFromFS(_ string, _ http.FileSystem) {}

func (_ *Context) FormFile(_ string) (*multipart.FileHeader, error) {
	return nil, nil
}

func (_ *Context) FullPath() string {
	return ""
}

func (_ *Context) Get(_ string) (interface{}, bool) {
	return nil, false
}

func (_ *Context) GetBool(_ string) bool {
	return false
}

func (_ *Context) GetDuration(_ string) time.Duration {
	return 0
}

func (_ *Context) GetFloat64(_ string) float64 {
	return 0
}

func (_ *Context) GetHeader(_ string) string {
	return ""
}

func (_ *Context) GetInt(_ string) int {
	return 0
}

func (_ *Context) GetInt64(_ string) int64 {
	return 0
}

func (_ *Context) GetPostForm(_ string) (string, bool) {
	return "", false
}

func (_ *Context) GetPostFormArray(_ string) ([]string, bool) {
	return nil, false
}

func (_ *Context) GetPostFormMap(_ string) (map[string]string, bool) {
	return nil, false
}

func (_ *Context) GetQuery(_ string) (string, bool) {
	return "", false
}

func (_ *Context) GetQueryArray(_ string) ([]string, bool) {
	return nil, false
}

func (_ *Context) GetQueryMap(_ string) (map[string]string, bool) {
	return nil, false
}

func (_ *Context) GetRawData() ([]byte, error) {
	return nil, nil
}

func (_ *Context) GetString(_ string) string {
	return ""
}

func (_ *Context) GetStringMap(_ string) map[string]interface{} {
	return nil
}

func (_ *Context) GetStringMapString(_ string) map[string]string {
	return nil
}

func (_ *Context) GetStringMapStringSlice(_ string) map[string][]string {
	return nil
}

func (_ *Context) GetStringSlice(_ string) []string {
	return nil
}

func (_ *Context) GetTime(_ string) time.Time {
	return time.Time{}
}

func (_ *Context) HTML(_ int, _ string, _ interface{}) {}

func (_ *Context) Handler() HandlerFunc {
	return nil
}

func (_ *Context) HandlerName() string {
	return ""
}

func (_ *Context) HandlerNames() []string {
	return nil
}

func (_ *Context) Header(_ string, _ string) {}

func (_ *Context) IndentedJSON(_ int, _ interface{}) {}

func (_ *Context) IsAborted() bool {
	return false
}

func (_ *Context) IsWebsocket() bool {
	return false
}

func (_ *Context) JSON(_ int, _ interface{}) {}

func (_ *Context) JSONP(_ int, _ interface{}) {}

func (_ *Context) MultipartForm() (*multipart.Form, error) {
	return nil, nil
}

func (_ *Context) MustBindWith(_ interface{}, _ interface{}) error {
	return nil
}

func (_ *Context) MustGet(_ string) interface{} {
	return nil
}

func (_ *Context) Negotiate(_ int, _ Negotiate) {}

func (_ *Context) NegotiateFormat(_ ...string) string {
	return ""
}

func (_ *Context) Next() {}

func (_ *Context) Param(_ string) string {
	return ""
}

func (_ *Context) PostForm(_ string) string {
	return ""
}

func (_ *Context) PostFormArray(_ string) []string {
	return nil
}

func (_ *Context) PostFormMap(_ string) map[string]string {
	return nil
}

func (_ *Context) ProtoBuf(_ int, _ interface{}) {}

func (_ *Context) PureJSON(_ int, _ interface{}) {}

func (_ *Context) Query(_ string) string {
	return ""
}

func (_ *Context) QueryArray(_ string) []string {
	return nil
}

func (_ *Context) QueryMap(_ string) map[string]string {
	return nil
}

func (_ *Context) Redirect(_ int, _ string) {}

func (_ *Context) Render(_ int, _ interface{}) {}

func (_ *Context) SSEvent(_ string, _ interface{}) {}

func (_ *Context) SaveUploadedFile(_ *multipart.FileHeader, _ string) error {
	return nil
}

func (_ *Context) SecureJSON(_ int, _ interface{}) {}

func (_ *Context) Set(_ string, _ interface{}) {}

func (_ *Context) SetAccepted(_ ...string) {}

func (_ *Context) SetCookie(_ string, _ string, _ int, _ string, _ string, _ bool, _ bool) {}

func (_ *Context) SetSameSite(_ http.SameSite) {}

func (_ *Context) ShouldBind(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindBodyWith(_ interface{}, _ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindHeader(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindJSON(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindQuery(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindUri(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindWith(_ interface{}, _ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindXML(_ interface{}) error {
	return nil
}

func (_ *Context) ShouldBindYAML(_ interface{}) error {
	return nil
}

func (_ *Context) Status(_ int) {}

func (_ *Context) Stream(_ func(io.Writer) bool) bool {
	return false
}

func (_ *Context) String(_ int, _ string, _ ...interface{}) {}

func (_ *Context) Value(_ interface{}) interface{} {
	return nil
}

func (_ *Context) XML(_ int, _ interface{}) {}

func (_ *Context) YAML(_ int, _ interface{}) {}

func Default() *Engine {
	return nil
}

type Engine struct {
	RouterGroup            RouterGroup
	RedirectTrailingSlash  bool
	RedirectFixedPath      bool
	HandleMethodNotAllowed bool
	ForwardedByClientIP    bool
	AppEngine              bool
	UseRawPath             bool
	UnescapePathValues     bool
	MaxMultipartMemory     int64
	RemoveExtraSlash       bool
	HTMLRender             interface{}
	FuncMap                template0.FuncMap
}

func (_ *Engine) Any(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) BasePath() string {
	return ""
}

func (_ *Engine) DELETE(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) Delims(_ string, _ string) *Engine {
	return nil
}

func (_ *Engine) GET(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) Group(_ string, _ ...HandlerFunc) *RouterGroup {
	return nil
}

func (_ *Engine) HEAD(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) Handle(_ string, _ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) HandleContext(_ *Context) {}

func (_ *Engine) LoadHTMLFiles(_ ...string) {}

func (_ *Engine) LoadHTMLGlob(_ string) {}

func (_ *Engine) NoMethod(_ ...HandlerFunc) {}

func (_ *Engine) NoRoute(_ ...HandlerFunc) {}

func (_ *Engine) OPTIONS(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) PATCH(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) POST(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) PUT(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *Engine) Routes() RoutesInfo {
	return nil
}

func (_ *Engine) Run(_ ...string) error {
	return nil
}

func (_ *Engine) RunFd(_ int) error {
	return nil
}

func (_ *Engine) RunListener(_ net.Listener) error {
	return nil
}

func (_ *Engine) RunTLS(_ string, _ string, _ string) error {
	return nil
}

func (_ *Engine) RunUnix(_ string) error {
	return nil
}

func (_ *Engine) SecureJsonPrefix(_ string) *Engine {
	return nil
}

func (_ *Engine) ServeHTTP(_ http.ResponseWriter, _ *http.Request) {}

func (_ *Engine) SetFuncMap(_ template0.FuncMap) {}

func (_ *Engine) SetHTMLTemplate(_ *template.Template) {}

func (_ *Engine) Static(_ string, _ string) IRoutes {
	return nil
}

func (_ *Engine) StaticFS(_ string, _ http.FileSystem) IRoutes {
	return nil
}

func (_ *Engine) StaticFile(_ string, _ string) IRoutes {
	return nil
}

func (_ *Engine) Use(_ ...HandlerFunc) IRoutes {
	return nil
}

type Error struct {
	Err  error
	Type ErrorType
	Meta interface{}
}

func (_ Error) Error() string {
	return ""
}

func (_ *Error) IsType(_ ErrorType) bool {
	return false
}

func (_ *Error) JSON() interface{} {
	return nil
}

func (_ *Error) MarshalJSON() ([]byte, error) {
	return nil, nil
}

func (_ *Error) SetMeta(_ interface{}) *Error {
	return nil
}

func (_ *Error) SetType(_ ErrorType) *Error {
	return nil
}

type ErrorType uint64

type HandlerFunc func(*Context)

type HandlersChain []HandlerFunc

func (_ HandlersChain) Last() HandlerFunc {
	return nil
}

type IRoutes interface {
	Any(_ string, _ ...HandlerFunc) IRoutes
	DELETE(_ string, _ ...HandlerFunc) IRoutes
	GET(_ string, _ ...HandlerFunc) IRoutes
	HEAD(_ string, _ ...HandlerFunc) IRoutes
	Handle(_ string, _ string, _ ...HandlerFunc) IRoutes
	OPTIONS(_ string, _ ...HandlerFunc) IRoutes
	PATCH(_ string, _ ...HandlerFunc) IRoutes
	POST(_ string, _ ...HandlerFunc) IRoutes
	PUT(_ string, _ ...HandlerFunc) IRoutes
	Static(_ string, _ string) IRoutes
	StaticFS(_ string, _ http.FileSystem) IRoutes
	StaticFile(_ string, _ string) IRoutes
	Use(_ ...HandlerFunc) IRoutes
}

type Negotiate struct {
	Offered  []string
	HTMLName string
	HTMLData interface{}
	JSONData interface{}
	XMLData  interface{}
	YAMLData interface{}
	Data     interface{}
}

type Param struct {
	Key   string
	Value string
}

type Params []Param

func (_ Params) ByName(_ string) string {
	return ""
}

func (_ Params) Get(_ string) (string, bool) {
	return "", false
}

type ResponseWriter interface {
	CloseNotify() <-chan bool
	Flush()
	Header() http.Header
	Hijack() (net.Conn, *bufio.ReadWriter, error)
	Pusher() http.Pusher
	Size() int
	Status() int
	Write(_ []byte) (int, error)
	WriteHeader(_ int)
	WriteHeaderNow()
	WriteString(_ string) (int, error)
	Written() bool
}

type RouteInfo struct {
	Method      string
	Path        string
	Handler     string
	HandlerFunc HandlerFunc
}

type RouterGroup struct {
	Handlers HandlersChain
}

func (_ *RouterGroup) Any(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) BasePath() string {
	return ""
}

func (_ *RouterGroup) DELETE(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) GET(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) Group(_ string, _ ...HandlerFunc) *RouterGroup {
	return nil
}

func (_ *RouterGroup) HEAD(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) Handle(_ string, _ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) OPTIONS(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) PATCH(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) POST(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) PUT(_ string, _ ...HandlerFunc) IRoutes {
	return nil
}

func (_ *RouterGroup) Static(_ string, _ string) IRoutes {
	return nil
}

func (_ *RouterGroup) StaticFS(_ string, _ http.FileSystem) IRoutes {
	return nil
}

func (_ *RouterGroup) StaticFile(_ string, _ string) IRoutes {
	return nil
}

func (_ *RouterGroup) Use(_ ...HandlerFunc) IRoutes {
	return nil
}

type RoutesInfo []RouteInfo
