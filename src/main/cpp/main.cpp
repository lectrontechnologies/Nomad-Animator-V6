// Nomad Animator - editor/animador 3D em C++ + OpenGL ES 3.0 (NativeActivity)
#include <android_native_app_glue.h>
#include <android/log.h>
#include <EGL/egl.h>
#include <GLES3/gl3.h>
#include <GLES3/gl31.h>
#include <cmath>
#include <cstring>
#include <vector>
#include <algorithm>
#include <ctime>
#include <cstdio>
#include <cstdarg>
#include <cstdint>
#include <string>
#include <dirent.h>
#define STB_TRUETYPE_IMPLEMENTATION
#include "stb_truetype.h"
#define CGLTF_IMPLEMENTATION
#include "cgltf.h"
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"
#include <sys/stat.h>
#include <zlib.h>
#include <cctype>
#define PI 3.14159265f

// ---------- matematica ----------
struct V{float x=0,y=0,z=0;};
V operator+(V a,V b){return{a.x+b.x,a.y+b.y,a.z+b.z};}
V operator-(V a,V b){return{a.x-b.x,a.y-b.y,a.z-b.z};}
V operator*(V a,float k){return{a.x*k,a.y*k,a.z*k};}
float dot(V a,V b){return a.x*b.x+a.y*b.y+a.z*b.z;}
V cross(V a,V b){return{a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x};}
V norm(V a){return a*(1/sqrtf(dot(a,a)));}
V lerp(V a,V b,float t){return a+(b-a)*t;}
struct M{float m[16];};
M id(){M r={};r.m[0]=r.m[5]=r.m[10]=r.m[15]=1;return r;}
M mul(const M&a,const M&b){M r;for(int c=0;c<4;c++)for(int i=0;i<4;i++){float s=0;for(int k=0;k<4;k++)s+=a.m[k*4+i]*b.m[c*4+k];r.m[c*4+i]=s;}return r;}
M persp(float fy,float as,float n,float f){M r={};float t=1/tanf(fy/2);r.m[0]=t/as;r.m[5]=t;r.m[10]=(f+n)/(n-f);r.m[11]=-1;r.m[14]=2*f*n/(n-f);return r;}
M lookAt(V e,V c,V up){V f=norm(c-e),s=norm(cross(f,up)),u=cross(s,f);M r=id();
 r.m[0]=s.x;r.m[4]=s.y;r.m[8]=s.z;r.m[1]=u.x;r.m[5]=u.y;r.m[9]=u.z;r.m[2]=-f.x;r.m[6]=-f.y;r.m[10]=-f.z;
 r.m[12]=-dot(s,e);r.m[13]=-dot(u,e);r.m[14]=dot(f,e);return r;}
struct T{V p,r,s{1,1,1};};
M model(const T&t){
 float cx=cosf(t.r.x),sx=sinf(t.r.x),cy=cosf(t.r.y),sy=sinf(t.r.y),cz=cosf(t.r.z),sz=sinf(t.r.z);
 M a=id(),b=id(),c=id();
 a.m[5]=cx;a.m[6]=sx;a.m[9]=-sx;a.m[10]=cx;
 b.m[0]=cy;b.m[2]=-sy;b.m[8]=sy;b.m[10]=cy;
 c.m[0]=cz;c.m[1]=sz;c.m[4]=-sz;c.m[5]=cz;
 M r=mul(c,mul(b,a));
 for(int i=0;i<4;i++){r.m[i]*=t.s.x;r.m[4+i]*=t.s.y;r.m[8+i]*=t.s.z;}
 r.m[12]=t.p.x;r.m[13]=t.p.y;r.m[14]=t.p.z;return r;}

// ---------- cena + animacao ----------
struct Key{float t;T x;};
struct Obj{int mesh;V col;T cur;std::vector<Key> k;char nm[24]="";int parent=-1;float len=1;float met=0,rou=.5f;int skin=-1;};
std::vector<Obj> objs;
int sel=-1,tool=3,W=1,H=1;      // tool: 0 mover,1 girar,2 escalar,3 camera
bool playing=false;float tm=1/24.f;float DUR=10;int gFS=1,gFE=240,gVS=1,gVE=120,gPlayDir=1;
void syncRange(){DUR=gFE/24.f;if(gVE>gFE)gVE=gFE;if(gVS<gFS)gVS=gFS;if(gVE-gVS<5)gVE=std::min(gFE,gVS+5);}
float yaw=.6f,pitch=.4f,cd=8;V tgt{0,.5f,0};const float FOV=1.047f;
V camEye(){return tgt+V{cosf(pitch)*sinf(yaw),sinf(pitch),cosf(pitch)*cosf(yaw)}*cd;}
static void qmulE(const float*a,const float*b,float*o){o[0]=a[3]*b[0]+a[0]*b[3]+a[1]*b[2]-a[2]*b[1];o[1]=a[3]*b[1]-a[0]*b[2]+a[1]*b[3]+a[2]*b[0];
 o[2]=a[3]*b[2]+a[0]*b[1]-a[1]*b[0]+a[2]*b[3];o[3]=a[3]*b[3]-a[0]*b[0]-a[1]*b[1]-a[2]*b[2];}
static void e2q(V r,float*q){float a[4]={sinf(r.x/2),0,0,cosf(r.x/2)},b[4]={0,sinf(r.y/2),0,cosf(r.y/2)},c[4]={0,0,sinf(r.z/2),cosf(r.z/2)},t[4];qmulE(b,a,t);qmulE(c,t,q);}
static V q2e(const float*q){float x=q[0],y=q[1],z=q[2],w=q[3];return V{atan2f(2*(w*x+y*z),1-2*(x*x+y*y)),asinf(std::clamp(2*(w*y-z*x),-1.f,1.f)),atan2f(2*(w*z+x*y),1-2*(y*y+z*z))};}
static V slerpE(V a,V b,float u){float qa[4],qb[4],q[4];e2q(a,qa);e2q(b,qb);float d=qa[0]*qb[0]+qa[1]*qb[1]+qa[2]*qb[2]+qa[3]*qb[3];
 if(d<0){for(int i=0;i<4;i++)qb[i]=-qb[i];d=-d;}float wa,wb;
 if(d>.9995f){wa=1-u;wb=u;}else{float th=acosf(d),sn=sinf(th);wa=sinf((1-u)*th)/sn;wb=sinf(u*th)/sn;}
 for(int i=0;i<4;i++)q[i]=qa[i]*wa+qb[i]*wb;float l=sqrtf(q[0]*q[0]+q[1]*q[1]+q[2]*q[2]+q[3]*q[3]);for(int i=0;i<4;i++)q[i]/=l;return q2e(q);}
T eval(Obj&o,float t){
 auto&k=o.k;if(k.empty())return o.cur;
 if(t<=k.front().t)return k.front().x;if(t>=k.back().t)return k.back().x;
 size_t i=0;while(k[i+1].t<t)i++;
 float u=(t-k[i].t)/(k[i+1].t-k[i].t);T r;
 r.p=lerp(k[i].x.p,k[i+1].x.p,u);r.r=slerpE(k[i].x.r,k[i+1].x.r,u);r.s=lerp(k[i].x.s,k[i+1].x.s,u);return r;}
void applyAnim(){for(auto&o:objs)if(!o.k.empty())o.cur=eval(o,tm);}
struct Skin{std::vector<int> j;std::vector<M> ibm,fz;};std::vector<Skin> skins;
M worldM(int i,int d=0){M l=model(objs[i].cur);int p=objs[i].parent;return(p>=0&&d<32)?mul(worldM(p,d+1),l):l;}
V wp(int i){M m=worldM(i);return V{m.m[12],m.m[13],m.m[14]};}
V invPt(const M&m,V p){V c0{m.m[0],m.m[1],m.m[2]},c1{m.m[4],m.m[5],m.m[6]},c2{m.m[8],m.m[9],m.m[10]},d=p-V{m.m[12],m.m[13],m.m[14]};
 float det=dot(c0,cross(c1,c2));if(fabsf(det)<1e-8f)return d;return V{dot(cross(c1,c2),d),dot(cross(c2,c0),d),dot(cross(c0,c1),d)}*(1/det);}
M invAff(const M&m){V c0{m.m[0],m.m[1],m.m[2]},c1{m.m[4],m.m[5],m.m[6]},c2{m.m[8],m.m[9],m.m[10]};float det=dot(c0,cross(c1,c2));M r=id();if(fabsf(det)<1e-12f)return r;
 V r0=cross(c1,c2)*(1/det),r1=cross(c2,c0)*(1/det),r2=cross(c0,c1)*(1/det);
 r.m[0]=r0.x;r.m[4]=r0.y;r.m[8]=r0.z;r.m[1]=r1.x;r.m[5]=r1.y;r.m[9]=r1.z;r.m[2]=r2.x;r.m[6]=r2.y;r.m[10]=r2.z;
 V t{m.m[12],m.m[13],m.m[14]};r.m[12]=-(r0.x*t.x+r0.y*t.y+r0.z*t.z);r.m[13]=-(r1.x*t.x+r1.y*t.y+r1.z*t.z);r.m[14]=-(r2.x*t.x+r2.y*t.y+r2.z*t.z);return r;}
T decomp(const M&m){T t;t.p=V{m.m[12],m.m[13],m.m[14]};
 float sx=sqrtf(m.m[0]*m.m[0]+m.m[1]*m.m[1]+m.m[2]*m.m[2]),sy=sqrtf(m.m[4]*m.m[4]+m.m[5]*m.m[5]+m.m[6]*m.m[6]),sz=sqrtf(m.m[8]*m.m[8]+m.m[9]*m.m[9]+m.m[10]*m.m[10]);
 if(sx>1e-8f&&sy>1e-8f&&sz>1e-8f){t.s=V{sx,sy,sz};t.r.y=asinf(std::clamp(-m.m[2]/sx,-1.f,1.f));t.r.x=atan2f(m.m[6]/sy,m.m[10]/sz);t.r.z=atan2f(m.m[1]/sx,m.m[0]/sx);}
 return t;}
void rotateWorld(Obj&ob,int a,float ang){
 M Pr=id();if(ob.parent>=0){M Pw=worldM(ob.parent);for(int c=0;c<3;c++){float L=sqrtf(Pw.m[c*4]*Pw.m[c*4]+Pw.m[c*4+1]*Pw.m[c*4+1]+Pw.m[c*4+2]*Pw.m[c*4+2]);
  if(L>1e-8f)for(int r=0;r<3;r++)Pr.m[c*4+r]=Pw.m[c*4+r]/L;}}
 M Pi=id();for(int c=0;c<3;c++)for(int r=0;r<3;r++)Pi.m[c*4+r]=Pr.m[r*4+c];
 T tt=ob.cur;tt.p=V{0,0,0};tt.s=V{1,1,1};M Lr=model(tt);
 M R=id();float c_=cosf(ang),s_=sinf(ang);
 if(a==0){R.m[5]=c_;R.m[6]=s_;R.m[9]=-s_;R.m[10]=c_;}else if(a==1){R.m[0]=c_;R.m[2]=-s_;R.m[8]=s_;R.m[10]=c_;}else{R.m[0]=c_;R.m[1]=s_;R.m[4]=-s_;R.m[5]=c_;}
 M Ln=mul(Pi,mul(R,mul(Pr,Lr)));ob.cur.r=decomp(Ln).r;}
void addObj(int mesh){
 static const V pal[]={{.9f,.35f,.3f},{.3f,.7f,.9f},{.5f,.85f,.4f},{.95f,.8f,.3f},{.7f,.45f,.9f}};
 Obj o;o.mesh=mesh;o.col=pal[objs.size()%5];static int cnt[6]={0,0,0,0,0,0};static const char*NM[6]={"Cube","Sphere","Plane","","","Bone"};snprintf(o.nm,24,"%s.%03d",NM[mesh],++cnt[mesh]);
 if(mesh==5){o.col={.85f,.85f,.65f};o.cur.p={0,0,0};if(sel>=0&&objs[sel].mesh==5){o.parent=sel;o.cur.p={0,objs[sel].len,0};}}
 else{o.cur.p={(objs.size()%4)*1.4f-2.1f,mesh==2?0.f:.5f,0};if(mesh==2)o.cur.s={2,2,2};}
 objs.push_back(o);sel=(int)objs.size()-1;}
void clearParent(int c){M w=worldM(c);objs[c].parent=-1;objs[c].cur=decomp(w);}
void delObj(int i){
 for(auto&sk:skins){if(sk.fz.size()<sk.j.size())sk.fz.assign(sk.j.size(),id());for(size_t k=0;k<sk.j.size();k++)if(sk.j[k]==i){sk.fz[k]=worldM(i);sk.j[k]=-1;}}
 int gp=objs[i].parent;
 for(int j=0;j<(int)objs.size();j++)if(objs[j].parent==i){M w=worldM(j);objs[j].parent=gp;objs[j].cur=decomp(gp>=0?mul(invAff(worldM(gp)),w):w);}
 objs.erase(objs.begin()+i);for(auto&o:objs)if(o.parent>i)o.parent--;sel=-1;
 for(auto&sk:skins)for(auto&jj:sk.j)if(jj>i)jj--;}

// ---------- GL ----------
const char*VS=R"(#version 300 es
layout(location=0) in vec3 aP; layout(location=1) in vec3 aN; layout(location=2) in vec4 aJ; layout(location=3) in vec4 aW;
uniform mat4 uMVP; uniform mat4 uM; uniform mat4 uJ[64]; uniform float uSk; out vec3 vN; out vec3 vP; out vec3 vW;
void main(){vec4 p=vec4(aP,1.0);vec3 n=aN;if(uSk>0.5){mat4 S=aW.x*uJ[int(aJ.x)]+aW.y*uJ[int(aJ.y)]+aW.z*uJ[int(aJ.z)]+aW.w*uJ[int(aJ.w)];p=S*p;n=mat3(S)*n;}
 gl_Position=uMVP*p; vN=mat3(uM)*n; vP=aP; vW=(uM*p).xyz;})";
const char*FS=R"(#version 300 es
precision highp float; in vec3 vN; in vec3 vP; in vec3 vW; uniform vec4 uC; uniform float uL; uniform vec3 uS; uniform vec3 uCam; uniform vec2 uMR; out vec4 o;
vec3 shade(vec3 L,vec3 Lc,vec3 N,vec3 V,vec3 alb,vec3 F0,float met,float rou){
 vec3 H=normalize(L+V);float a=rou*rou,a2=a*a;float NL=max(dot(N,L),0.0),NV=max(dot(N,V),1e-3),NH=max(dot(N,H),0.0),VH=max(dot(V,H),0.0);
 float dd=NH*NH*(a2-1.0)+1.0;float D=a2/(3.14159*dd*dd+1e-6);float k=(rou+1.0)*(rou+1.0)/8.0;
 float G=(NL/(NL*(1.0-k)+k))*(NV/(NV*(1.0-k)+k));vec3 F=F0+(1.0-F0)*pow(1.0-VH,5.0);
 vec3 spec=D*G*F/(4.0*NV*max(NL,1e-3));vec3 kd=(1.0-F)*(1.0-met);
 return (kd*alb/3.14159+spec)*Lc*NL;}
vec3 pbr(){vec3 N=normalize(vN),V=normalize(uCam-vW);if(dot(N,V)<0.0)N=-N;
 vec3 alb=pow(uC.rgb,vec3(2.2));float met=uMR.x,rou=clamp(uMR.y,0.05,1.0);vec3 F0=mix(vec3(0.04),alb,met);
 vec3 col=shade(normalize(vec3(.4,.8,.5)),vec3(3.2,3.0,2.8),N,V,alb,F0,met,rou)+shade(normalize(vec3(-.6,.3,-.4)),vec3(.6,.7,1.0),N,V,alb,F0,met,rou);
 vec3 amb=mix(vec3(.12,.11,.10),vec3(.22,.26,.34),N.y*.5+.5);float NV=max(dot(N,V),0.0);
 vec3 Fa=F0+(max(vec3(1.0-rou),F0)-F0)*pow(1.0-NV,5.0);
 col+=amb*(alb*(1.0-met)+Fa*0.6);
 col=col*(2.51*col+0.03)/(col*(2.43*col+0.59)+0.14);return pow(clamp(col,0.0,1.0),vec3(1.0/2.2));}
void main(){if(uL<-1.5){vec2 q=(vP.xy-.5)*uS.xy;float dd=(abs(q.x)+abs(q.y)-uS.x*.5)*.7071;o=vec4(uC.rgb,uC.a*clamp(.5-dd,0.0,1.0));return;} if(uL<0.0){vec2 q=(vP.xy-.5)*uS.xy;vec2 e=abs(q)-uS.xy*.5+uS.z;float dd=length(max(e,0.0))+min(max(e.x,e.y),0.0)-uS.z;o=vec4(uC.rgb,uC.a*clamp(.5-dd,0.0,1.0));return;} if(uL>0.5){o=vec4(pbr(),uC.a);return;} o=vec4(uC.rgb,uC.a);})";
GLuint uMVP,uM,uC,uL,uS,uCamL,uMRL,uJL,uSkL,gProg=0;float gS[3]={1,1,0},gMR[2]={0,.5f},gSk=0;void initText();void initPost();void initMC();
struct Mesh{GLuint vao=0,vbo=0;int n=0;GLenum mode=GL_TRIANGLES;std::vector<float> cpu;float rad=1;GLuint svbo=0;bool skinned=false;std::vector<float> skin;};
std::vector<Mesh> meshes(6); // 0 cubo,1 esfera,2 plano,3 quad2D,4 grade,5 osso
GLuint sh(GLenum t,const char*s){GLuint h=glCreateShader(t);glShaderSource(h,1,&s,0);glCompileShader(h);GLint ok;glGetShaderiv(h,GL_COMPILE_STATUS,&ok);
 if(!ok){char b[512];glGetShaderInfoLog(h,512,0,b);__android_log_print(ANDROID_LOG_ERROR,"NA","%s",b);}return h;}
void vtx(std::vector<float>&v,V p,V n){v.insert(v.end(),{p.x,p.y,p.z,n.x,n.y,n.z});}
Mesh upload(const std::vector<float>&v,GLenum mode){
 Mesh m;m.n=(int)v.size()/6;m.mode=mode;m.cpu=v;
 glGenVertexArrays(1,&m.vao);glGenBuffers(1,&m.vbo);glBindVertexArray(m.vao);glBindBuffer(GL_ARRAY_BUFFER,m.vbo);
 glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STATIC_DRAW);
 glEnableVertexAttribArray(0);glVertexAttribPointer(0,3,GL_FLOAT,GL_FALSE,24,(void*)0);
 glEnableVertexAttribArray(1);glVertexAttribPointer(1,3,GL_FLOAT,GL_FALSE,24,(void*)12);return m;}
void attachSkin(Mesh&m,const std::vector<float>&sk){
 glBindVertexArray(m.vao);glGenBuffers(1,&m.svbo);glBindBuffer(GL_ARRAY_BUFFER,m.svbo);glBufferData(GL_ARRAY_BUFFER,sk.size()*4,sk.data(),GL_STATIC_DRAW);
 glEnableVertexAttribArray(2);glVertexAttribPointer(2,4,GL_FLOAT,GL_FALSE,32,(void*)0);
 glEnableVertexAttribArray(3);glVertexAttribPointer(3,4,GL_FLOAT,GL_FALSE,32,(void*)16);m.skinned=true;m.skin=sk;}
void buildMeshes(){
 std::vector<float> a;
 V F[6][3]={{{1,0,0},{0,1,0},{0,0,1}},{{-1,0,0},{0,0,1},{0,1,0}},{{0,1,0},{0,0,1},{1,0,0}},
            {{0,-1,0},{1,0,0},{0,0,1}},{{0,0,1},{1,0,0},{0,1,0}},{{0,0,-1},{0,1,0},{1,0,0}}};
 int ix[6]={0,1,2,0,2,3};
 for(auto&f:F){V n=f[0],u=f[1],v=f[2],c=n*.5f;V p[4]={c-u*.5f-v*.5f,c+u*.5f-v*.5f,c+u*.5f+v*.5f,c-u*.5f+v*.5f};
  for(int i:ix)vtx(a,p[i],n);}
 meshes[0]=upload(a,GL_TRIANGLES);
 a.clear();
 auto sp=[](int i,int j){float th=i*PI/16,ph=j*2*PI/24;return V{sinf(th)*cosf(ph),cosf(th),sinf(th)*sinf(ph)};};
 for(int i=0;i<16;i++)for(int j=0;j<24;j++){V p=sp(i,j),q=sp(i+1,j),r=sp(i+1,j+1),s=sp(i,j+1);
  vtx(a,p*.5f,p);vtx(a,q*.5f,q);vtx(a,r*.5f,r);vtx(a,p*.5f,p);vtx(a,r*.5f,r);vtx(a,s*.5f,s);}
 meshes[1]=upload(a,GL_TRIANGLES);
 a.clear();V up{0,1,0};
 V pl[6]={{-1,0,-1},{-1,0,1},{1,0,1},{-1,0,-1},{1,0,1},{1,0,-1}};for(V p:pl)vtx(a,p,up);
 meshes[2]=upload(a,GL_TRIANGLES);
 a.clear();
 V qd[6]={{0,0,0},{1,0,0},{1,1,0},{0,0,0},{1,1,0},{0,1,0}};for(V p:qd)vtx(a,p,{0,0,1});
 meshes[3]=upload(a,GL_TRIANGLES);
 a.clear();
 for(int i=-10;i<=10;i++){vtx(a,{(float)i,0,-10},up);vtx(a,{(float)i,0,10},up);vtx(a,{-10,0,(float)i},up);vtx(a,{10,0,(float)i},up);}
 meshes[4]=upload(a,GL_LINES);
 a.clear();{V h{0,0,0},t{0,1,0};float w=.12f,y=.15f;V r[4]={{w,y,0},{0,y,w},{-w,y,0},{0,y,-w}};
  for(int i=0;i<4;i++){V p=r[i],q=r[(i+1)%4];V n1=norm(cross(p-h,q-h)),n2=norm(cross(q-t,p-t));
   vtx(a,h,n1);vtx(a,p,n1);vtx(a,q,n1);vtx(a,t,n2);vtx(a,q,n2);vtx(a,p,n2);}}
 meshes[5]=upload(a,GL_TRIANGLES);}
void initGL(){
 GLuint p=gProg=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,VS));glAttachShader(p,sh(GL_FRAGMENT_SHADER,FS));
 glLinkProgram(p);glUseProgram(p);
 uMVP=glGetUniformLocation(p,"uMVP");uM=glGetUniformLocation(p,"uM");uC=glGetUniformLocation(p,"uC");uL=glGetUniformLocation(p,"uL");uS=glGetUniformLocation(p,"uS");uCamL=glGetUniformLocation(p,"uCam");uJL=glGetUniformLocation(p,"uJ");uSkL=glGetUniformLocation(p,"uSk");uMRL=glGetUniformLocation(p,"uMR");
 glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);buildMeshes();for(size_t i=6;i<meshes.size();i++){std::vector<float> c=meshes[i].cpu,sk=meshes[i].skin;float r=meshes[i].rad;meshes[i]=upload(c,GL_TRIANGLES);meshes[i].rad=r;if(!sk.empty())attachSkin(meshes[i],sk);}initText();initPost();initMC();}
void draw(Mesh&m,const M&mvp,const M&mod,float r,float g,float b,float a,float lit){
 glUniformMatrix4fv(uMVP,1,GL_FALSE,mvp.m);glUniformMatrix4fv(uM,1,GL_FALSE,mod.m);
 glUniform4f(uC,r,g,b,a);glUniform1f(uL,lit);glUniform3f(uS,gS[0],gS[1],gS[2]);glUniform2f(uMRL,gMR[0],gMR[1]);glUniform1f(uSkL,gSk);glBindVertexArray(m.vao);glDrawArrays(m.mode,0,m.n);}

// ---------- UI 2D ----------
void rect(float x,float y,float w,float h,float r,float g,float b,float a=1,float rad=0){
 M m={};m.m[0]=2*w/W;m.m[5]=-2*h/H;m.m[10]=1;m.m[12]=2*x/W-1;m.m[13]=1-2*y/H;m.m[15]=1;
 gS[0]=w;gS[1]=h;gS[2]=std::min(rad,std::min(w,h)/2);draw(meshes[3],m,id(),r,g,b,a,-1);}
const char*GN="ABCDEHIKLMNOPRSTUVYXZ0123456789";
const char*GG[]={"010101111101101","110101110101110","011100100100011","110101101101110","111100110100111",
 "101101111101101","111010010010111","101101110101101","100100100100111","101111111101101","110101101101101",
 "010101101101010","110101110100100","110101110101101","011100010001110","111010010010010","101101101101111",
 "101101101101010","101101010010010","101101010101101","111001010100111","111101101101111","010110010010111","111001111100111","111001111001111","101101111001001","111100111001111","111100111101111","111001001010010","111101111101111","111101111001111"};
void btext(const char*s,float x,float y,float ps,float r,float g,float b){
 for(;*s;s++){const char*p=strchr(GN,*s);
  if(p){const char*gl=GG[p-GN];for(int k=0;k<15;k++)if(gl[k]=='1')rect(x+(k%3)*ps,y+(k/3)*ps,ps,ps,r,g,b);}
  x+=4*ps;}}
// ---- fonte TTF do sistema (stb_truetype) ----
std::vector<unsigned char> gAtlas;stbtt_bakedchar gBC[96];GLuint gTex=0,gTP=0,gTVao=0,gTVbo=0,uTS,uTC;
const float FPX=44;
bool loadFont(){
 FILE*f=nullptr;
 static const char*P[]={"/system/fonts/Roboto-Regular.ttf","/system/fonts/RobotoStatic-Regular.ttf","/system/fonts/Roboto[wdth,wght].ttf","/system/fonts/NotoSans-Regular.ttf","/system/fonts/DroidSans.ttf"};
 for(auto q:P){f=fopen(q,"rb");if(f)break;}
 for(int pass=0;pass<2&&!f;pass++){if(DIR*dr=opendir("/system/fonts")){while(dirent*en=readdir(dr)){std::string n=en->d_name;
  bool ttf=n.size()>8&&n.compare(n.size()-4,4,".ttf")==0,bad=false;
  for(const char*w:{"Italic","Bold","Light","Thin","Medium","Black","Mono","Slab","Serif","Emoji","Symbols","Cjk","CJK","Condensed"})if(n.find(w)!=std::string::npos)bad=true;
  bool ok=pass==0?n.find("Roboto")!=std::string::npos:n.find("Regular")!=std::string::npos;
  if(ttf&&ok&&!bad){f=fopen(("/system/fonts/"+n).c_str(),"rb");if(f)break;}}closedir(dr);}}
 if(!f)return false;
 fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);std::vector<unsigned char> d(sz>0?sz:1);
 size_t rd=fread(d.data(),1,sz,f);fclose(f);if(sz<=0||(long)rd!=sz)return false;
 gAtlas.assign(512*512,0);
 if(stbtt_BakeFontBitmap(d.data(),0,FPX,gAtlas.data(),512,512,32,96,gBC)<=0){gAtlas.clear();return false;}
 return true;}
void initText(){
 static bool tried=false;if(!tried){tried=true;loadFont();}
 gTex=0;if(gAtlas.empty())return;
 const char*vs="#version 300 es\nlayout(location=0) in vec4 aV; uniform vec2 uScr; out vec2 vT;\nvoid main(){gl_Position=vec4(aV.x/uScr.x*2.0-1.0,1.0-aV.y/uScr.y*2.0,0.0,1.0); vT=aV.zw;}";
 const char*fs="#version 300 es\nprecision mediump float; in vec2 vT; uniform sampler2D uTex; uniform vec4 uC; out vec4 o;\nvoid main(){o=vec4(uC.rgb,uC.a*texture(uTex,vT).r);}";
 GLuint p=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,vs));glAttachShader(p,sh(GL_FRAGMENT_SHADER,fs));glLinkProgram(p);gTP=p;
 uTS=glGetUniformLocation(p,"uScr");uTC=glGetUniformLocation(p,"uC");glUseProgram(p);glUniform1i(glGetUniformLocation(p,"uTex"),0);glUseProgram(gProg);
 glGenTextures(1,&gTex);glBindTexture(GL_TEXTURE_2D,gTex);glPixelStorei(GL_UNPACK_ALIGNMENT,1);
 glTexImage2D(GL_TEXTURE_2D,0,GL_R8,512,512,0,GL_RED,GL_UNSIGNED_BYTE,gAtlas.data());
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_LINEAR);
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);
 glGenVertexArrays(1,&gTVao);glGenBuffers(1,&gTVbo);glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);
 glEnableVertexAttribArray(0);glVertexAttribPointer(0,4,GL_FLOAT,GL_FALSE,16,(void*)0);}
float tw(const char*s,float ps){if(!gTex)return strlen(s)*4*ps-ps;float w=0;for(;*s;s++){int c=(unsigned char)*s;if(c>=32&&c<128)w+=gBC[c-32].xadvance;}return w*ps*7/FPX;}
void text(const char*s,float x,float y,float ps,float r,float g,float b){
 if(!gTex){btext(s,x,y,ps,r,g,b);return;}
 float sc=ps*7/FPX,by=y+5*ps;std::vector<float> v;
 for(;*s;s++){int c=(unsigned char)*s;if(c<32||c>=128)continue;stbtt_aligned_quad q;float xp=0,yp=0;stbtt_GetBakedQuad(gBC,512,512,c-32,&xp,&yp,&q,1);
  float x0=x+q.x0*sc,x1=x+q.x1*sc,y0=by+q.y0*sc,y1=by+q.y1*sc;
  v.insert(v.end(),{x0,y0,q.s0,q.t0,x1,y0,q.s1,q.t0,x1,y1,q.s1,q.t1,x0,y0,q.s0,q.t0,x1,y1,q.s1,q.t1,x0,y1,q.s0,q.t1});x+=xp*sc;}
 if(v.empty())return;
 glUseProgram(gTP);glUniform2f(uTS,(float)W,(float)H);glUniform4f(uTC,r,g,b,1);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gTex);
 glBindVertexArray(gTVao);glBindBuffer(GL_ARRAY_BUFFER,gTVbo);glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STREAM_DRAW);
 glDrawArrays(GL_TRIANGLES,0,(int)v.size()/4);glUseProgram(gProg);}
struct Rc{float x,y,w,h;};struct Btn{Rc r;int id;};
std::vector<Btn> gBtn;std::vector<Rc> gBlock;Rc gTrack={0,0,0,0};
float U(){return H*.01f;}
bool inR(const Rc&r,float x,float y){return x>=r.x&&x<=r.x+r.w&&y>=r.y&&y<=r.y+r.h;}
void dia(float cx,float cy,float sz,float r,float g,float b){M m={};m.m[0]=2*sz/W;m.m[5]=-2*sz/H;m.m[10]=1;m.m[12]=2*(cx-sz/2)/W-1;m.m[13]=1-2*(cy-sz/2)/H;m.m[15]=1;
 gS[0]=sz;gS[1]=sz;gS[2]=0;draw(meshes[3],m,id(),r,g,b,1,-2);}
void tcen(const char*s,float cx,float cy,float ps,float r,float g,float b){text(s,cx-tw(s,ps)/2,cy-2.5f*ps,ps,r,g,b);}
void panel(float x,float y,float w,float h,float rad){rect(x,y,w,h,.13f,.13f,.14f,.9f,rad);gBlock.push_back({x,y,w,h});}
void pill(float x,float y,float w,float h,int bid,const char*lb,bool on,float cr,float cg,float cb){
 if(on){cr=.28f;cg=.45f;cb=.70f;}
 rect(x,y,w,h,cr,cg,cb,1,h*.28f);tcen(lb,x+w/2,y+h/2,h*.072f,.94f,.94f,.94f);gBtn.push_back({{x,y,w,h},bid});}
void icon(int bid,float cx,float cy,float s,bool on){
 float br=on?.28f:.33f,bg=on?.45f:.33f,bb=on?.70f:.35f;
 if(bid==6){rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s);rect(cx-s*.7f,cy-s*.7f,1.4f*s,1.4f*s,br,bg,bb,1,s*.7f);rect(cx-s*.22f,cy-s*.22f,s*.44f,s*.44f,.92f,.92f,.92f,1,s*.22f);}
 else if(bid==3){rect(cx-s,cy-s*.09f,2*s,s*.18f,.92f,.92f,.92f);rect(cx-s*.09f,cy-s,s*.18f,2*s,.92f,.92f,.92f);
  dia(cx-s,cy,s*.7f,.92f,.92f,.92f);dia(cx+s,cy,s*.7f,.92f,.92f,.92f);dia(cx,cy-s,s*.7f,.92f,.92f,.92f);dia(cx,cy+s,s*.7f,.92f,.92f,.92f);}
 else if(bid==4){rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s);rect(cx-s*.66f,cy-s*.66f,1.32f*s,1.32f*s,br,bg,bb,1,s*.66f);rect(cx+s*.42f,cy-s*.9f,s*.45f,s*.45f,1,.8f,.2f,1,s*.22f);}
 else{rect(cx-s,cy-s,2*s,2*s,.92f,.92f,.92f,1,s*.18f);rect(cx-s*.78f,cy-s*.78f,1.56f*s,1.56f*s,br,bg,bb,1,s*.1f);rect(cx-s*.55f,cy-s*.55f,s*.7f,s*.7f,.92f,.92f,.92f,1,s*.08f);}}
const char*BL[10]={"CUBE","SPH","PLN","MOVE","ROT","SCL","CAM","KEY","PLAY","DEL"};
float BC[10][3]={{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.6f,.3f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.2f,.4f,.8f},{.9f,.75f,.1f},{.9f,.5f,.1f},{.8f,.2f,.2f}};
float ML(){return W*.04f;} float bw(){return (W-2*ML())/10.f;} float bh(){return H*.1f;} float tlh(){return H*.09f;} float tly(){return H-H*.045f-tlh();}
float gTX0=0,gTW=1;float tx(float t){return gTX0+(t*24-gVS)/(float)std::max(gVE-gVS,1)*gTW;}

// ---------- EGL ----------
EGLDisplay dpy=EGL_NO_DISPLAY;EGLSurface surf=EGL_NO_SURFACE;EGLContext ctx=EGL_NO_CONTEXT;bool ready=false;
bool initEGL(ANativeWindow*w){
 dpy=eglGetDisplay(EGL_DEFAULT_DISPLAY);eglInitialize(dpy,0,0);
 EGLint ca[]={EGL_RENDERABLE_TYPE,0x0040,EGL_SURFACE_TYPE,EGL_WINDOW_BIT,EGL_RED_SIZE,8,EGL_GREEN_SIZE,8,EGL_BLUE_SIZE,8,EGL_DEPTH_SIZE,24,EGL_SAMPLE_BUFFERS,1,EGL_SAMPLES,4,EGL_NONE};
 EGLConfig cfg;EGLint n=0;eglChooseConfig(dpy,ca,&cfg,1,&n);if(!n){ca[12]=EGL_NONE;eglChooseConfig(dpy,ca,&cfg,1,&n);}if(!n)return false;
 EGLint fmt;eglGetConfigAttrib(dpy,cfg,EGL_NATIVE_VISUAL_ID,&fmt);ANativeWindow_setBuffersGeometry(w,0,0,fmt);
 surf=eglCreateWindowSurface(dpy,cfg,w,0);
 const EGLint xa[]={EGL_CONTEXT_CLIENT_VERSION,3,EGL_NONE};ctx=eglCreateContext(dpy,cfg,0,xa);
 if(!eglMakeCurrent(dpy,surf,surf,ctx))return false;
 eglQuerySurface(dpy,surf,EGL_WIDTH,&W);eglQuerySurface(dpy,surf,EGL_HEIGHT,&H);return true;}
void termEGL(){
 if(dpy!=EGL_NO_DISPLAY){eglMakeCurrent(dpy,EGL_NO_SURFACE,EGL_NO_SURFACE,EGL_NO_CONTEXT);
  if(ctx!=EGL_NO_CONTEXT)eglDestroyContext(dpy,ctx);if(surf!=EGL_NO_SURFACE)eglDestroySurface(dpy,surf);eglTerminate(dpy);}
 dpy=EGL_NO_DISPLAY;ctx=EGL_NO_CONTEXT;surf=EGL_NO_SURFACE;}

// ---------- render ----------
M gVP;int gAxis=-1,gIdx=0;bool gDrag=false;
const V AX[3]={{1,0,0},{0,1,0},{0,0,1}};
const float AC[3][3]={{.9f,.25f,.25f},{.4f,.8f,.3f},{.3f,.5f,1.f}};
float gl(){return cd*.2f;}
bool prj(V p,float&x,float&y){const float*m=gVP.m;
 float cx=m[0]*p.x+m[4]*p.y+m[8]*p.z+m[12],cy=m[1]*p.x+m[5]*p.y+m[9]*p.z+m[13],cw=m[3]*p.x+m[7]*p.y+m[11]*p.z+m[15];
 if(cw<.01f)return false;x=(cx/cw*.5f+.5f)*W;y=(1-(cy/cw*.5f+.5f))*H;return true;}
V ringPt(int a,int i){float th=i*2*PI/32,c=cosf(th)*gl()*.8f,s=sinf(th)*gl()*.8f;V o=wp(sel);
 return a==0?o+V{0,c,s}:a==1?o+V{s,0,c}:o+V{c,s,0};}
int hitGizmo(float x,float y){
 if(sel<0||tool>2)return -1;
 V o=wp(sel);float ox,oy;if(!prj(o,ox,oy))return -1;
 int best=-1;float bd=48;
 for(int a=0;a<3;a++){float d=1e9f;int bi=0;
  if(tool==1){for(int i=0;i<32;i++){float px,py;if(prj(ringPt(a,i),px,py)){float dd=hypotf(px-x,py-y);if(dd<d){d=dd;bi=i;}}}}
  else{float ex,ey;if(prj(o+AX[a]*gl(),ex,ey)){float vx=ex-ox,vy=ey-oy,t=std::clamp(((x-ox)*vx+(y-oy)*vy)/(vx*vx+vy*vy+1e-3f),0.f,1.f);d=hypotf(x-ox-vx*t,y-oy-vy*t);}}
  if(d<bd){bd=d;best=a;gIdx=bi;}}
 return best;}
void drawGizmo(){
 V p=wp(sel);float L=gl(),th=L*.025f;
 auto box=[&](V c,V sc,const float*k,int ms=0){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[ms],mul(gVP,m),m,k[0],k[1],k[2],1,0);};
 static const float Y[3]={1,.9f,.2f};
 for(int a=0;a<3;a++){const float*k=(gDrag&&a==gAxis)?Y:AC[a];
  if(tool==1){for(int i=0;i<32;i++)box(ringPt(a,i),V{th*3,th*3,th*3},k,1);}
  else{V sc{th,th,th};(&sc.x)[a]=L;box(p+AX[a]*(L*.5f),sc,k);float e=th*(tool==2?7.f:4.f);box(p+AX[a]*L,V{e,e,e},k,1);}}}
struct ND{float x,y,z;int a;bool pos;};
float navR(){return H*.1f;} float navX(){return W-ML()-navR()-H*.01f;} float navY(){return H*.072f+navR()+H*.02f;}
void navPts(ND*d){V f=norm(tgt-camEye()),s=norm(cross(f,V{0,1,0})),u=cross(s,f);float R=navR();
 for(int i=0;i<6;i++){int a=i%3;V v=AX[a]*(i<3?1.f:-1.f);d[i]={navX()+dot(v,s)*R*.72f,navY()-dot(v,u)*R*.72f,dot(v,f),a,i<3};}}
void drawNav(){ND d[6];navPts(d);float R=navR(),cx=navX(),cy=navY();
 rect(cx-R-6,cy-R-6,2*R+12,2*R+12,0,0,0,.3f,R+6);
 std::sort(d,d+6,[](const ND&p,const ND&q){return p.z>q.z;});
 static const char*LB[3]={"X","Y","Z"};
 for(auto&e:d){const float*c=AC[e.a];float k=e.pos?1.f:.5f,r=e.pos?H*.024f:H*.017f;
  if(e.pos)for(int j=1;j<6;j++)rect(cx+(e.x-cx)*j/6-2,cy+(e.y-cy)*j/6-2,4,4,c[0],c[1],c[2],1,2);
  rect(e.x-r,e.y-r,2*r,2*r,c[0]*k,c[1]*k,c[2]*k,1,r);
  if(e.pos){float ps=H*.0055f;text(LB[e.a],e.x-tw(LB[e.a],ps)/2,e.y-2.5f*ps,ps,1,1,1);}}}
// ---------- exportacao (MAD / glTF) + rigging ----------
bool parentMode=false;std::string gToast;float gToastT=0;const char*gDir=".";std::string gProj="projeto";
void toast(const std::string&t){gToast=t;gToastT=4;}
std::string fm(const char*f,...){char b[1024];va_list a;va_start(a,f);vsnprintf(b,1024,f,a);va_end(a);return b;}
void insertKey(){if(sel<0)return;Obj&o=objs[sel];bool f=false;for(auto&k:o.k)if(fabsf(k.t-tm)<.02f){k.x=o.cur;f=true;}
 if(!f){o.k.push_back({tm,o.cur});std::sort(o.k.begin(),o.k.end(),[](const Key&a,const Key&b){return a.t<b.t;});}}
void setParent(int c,int p){for(int a=p;a>=0;a=objs[a].parent)if(a==c){toast("Nao pode: ciclo");return;}
 M w=worldM(c);objs[c].parent=p;objs[c].cur=decomp(mul(invAff(worldM(p)),w));toast("Parent definido");}
void finishParent(int h){parentMode=false;if(sel>=0&&h>=0&&h!=sel)setParent(sel,h);else toast("Cancelado");}
FILE*openOut(const char*ext,std::string&path,bool&fb){long t=(long)time(nullptr);fb=false;
 path=fm("/storage/emulated/0/Download/nomad_%ld.%s",t,ext);FILE*f=fopen(path.c_str(),"wb");
 if(!f){path=fm("%s/nomad_%ld.%s",gDir,t,ext);f=fopen(path.c_str(),"wb");fb=true;}return f;}
void saved(const std::string&path,bool fb){toast("Salvo: "+path+(fb?"  (ative Acesso a todos os arquivos para salvar em Downloads)":""));}
void writeMAD(FILE*f){
 auto U_=[&](uint32_t v){fwrite(&v,4,1,f);};auto Fl=[&](float v){fwrite(&v,4,1,f);};
 fwrite("MAD2",1,4,f);U_(2);Fl(24);Fl(DUR);U_((uint32_t)(meshes.size()-6));
 for(size_t i=6;i<meshes.size();i++){Mesh&m=meshes[i];U_((uint32_t)m.cpu.size());fwrite(m.cpu.data(),4,m.cpu.size(),f);Fl(m.rad);U_((uint32_t)m.skin.size());if(!m.skin.empty())fwrite(m.skin.data(),4,m.skin.size(),f);}
 U_((uint32_t)skins.size());
 for(auto&sk:skins){U_((uint32_t)sk.j.size());for(size_t k=0;k<sk.j.size();k++){U_((uint32_t)sk.j[k]);fwrite(sk.ibm[k].m,4,16,f);const M fz=k<sk.fz.size()?sk.fz[k]:id();fwrite(fz.m,4,16,f);}}
 U_((uint32_t)objs.size());
 for(auto&o:objs){U_((uint32_t)o.mesh);U_((uint32_t)o.parent);U_((uint32_t)o.skin);fwrite(o.nm,1,24,f);Fl(o.len);Fl(o.met);Fl(o.rou);Fl(o.col.x);Fl(o.col.y);Fl(o.col.z);
  const float*c=&o.cur.p.x;for(int i=0;i<9;i++)Fl(c[i]);U_((uint32_t)o.k.size());for(auto&k:o.k){Fl(k.t);const float*q=&k.x.p.x;for(int i=0;i<9;i++)Fl(q[i]);}}
 Fl(yaw);Fl(pitch);Fl(cd);Fl(tgt.x);Fl(tgt.y);Fl(tgt.z);Fl(tm);}
FILE*openOutName(const std::string&nm,const char*ext,std::string&path,bool&fb){fb=false;
 path=fm("/storage/emulated/0/Download/%s.%s",nm.c_str(),ext);FILE*f=fopen(path.c_str(),"wb");
 if(!f){path=fm("%s/%s.%s",gDir,nm.c_str(),ext);f=fopen(path.c_str(),"wb");fb=true;}return f;}
void exportMAD(){std::string path;bool fb;FILE*f=openOut("mad",path,fb);if(!f){toast("Erro ao salvar");return;}writeMAD(f);fclose(f);saved(path,fb);}
void saveProject(){std::string path;bool fb;FILE*f=openOutName(gProj,"mad",path,fb);if(!f){toast("Erro ao salvar");return;}writeMAD(f);fclose(f);saved(path,fb);}
std::string b64(const std::vector<unsigned char>&d){static const char*AB="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";std::string o;
 for(size_t i=0;i<d.size();i+=3){unsigned v=d[i]<<16;if(i+1<d.size())v|=d[i+1]<<8;if(i+2<d.size())v|=d[i+2];
  o+=AB[v>>18&63];o+=AB[v>>12&63];o+=i+1<d.size()?AB[v>>6&63]:'=';o+=i+2<d.size()?AB[v&63]:'=';}return o;}
void qm(const float*a,const float*b,float*o){o[0]=a[3]*b[0]+a[0]*b[3]+a[1]*b[2]-a[2]*b[1];o[1]=a[3]*b[1]-a[0]*b[2]+a[1]*b[3]+a[2]*b[0];
 o[2]=a[3]*b[2]+a[0]*b[1]-a[1]*b[0]+a[2]*b[3];o[3]=a[3]*b[3]-a[0]*b[0]-a[1]*b[1]-a[2]*b[2];}
void eq(V r,float*q){float a[4]={sinf(r.x/2),0,0,cosf(r.x/2)},b[4]={0,sinf(r.y/2),0,cosf(r.y/2)},c[4]={0,0,sinf(r.z/2),cosf(r.z/2)},t[4];qm(b,a,t);qm(c,t,q);}
std::string mm3(const std::vector<float>&v){float lo[3]={1e30f,1e30f,1e30f},hi[3]={-1e30f,-1e30f,-1e30f};
 for(size_t i=0;i+2<v.size();i+=3)for(int c=0;c<3;c++){lo[c]=std::min(lo[c],v[i+c]);hi[c]=std::max(hi[c],v[i+c]);}
 return fm(",\"min\":[%g,%g,%g],\"max\":[%g,%g,%g]",lo[0],lo[1],lo[2],hi[0],hi[1],hi[2]);}
void exportGLTF(){
 if(objs.empty()){toast("Cena vazia");return;}
 std::string path;bool fb;FILE*f=openOut("gltf",path,fb);if(!f){toast("Erro ao salvar");return;}
 std::vector<unsigned char> bin;std::string views,accs,meshJ,mats,nodes,samp,chn,roots;int nv=0,na=0,nm=0,ns=0;
 auto view=[&](const void*d,size_t n){while(bin.size()%4)bin.push_back(0);size_t off=bin.size();const unsigned char*c=(const unsigned char*)d;bin.insert(bin.end(),c,c+n);
  views+=fm("%s{\"buffer\":0,\"byteOffset\":%zu,\"byteLength\":%zu}",nv?",":"",off,n);return nv++;};
 auto acc=[&](const std::vector<float>&v,int comps,const char*ty,const std::string&mm){int vi=view(v.data(),v.size()*4);
  accs+=fm("%s{\"bufferView\":%d,\"componentType\":5126,\"count\":%d,\"type\":\"%s\"%s}",na?",":"",vi,(int)v.size()/comps,ty,mm.c_str());return na++;};
 std::vector<int> pa(meshes.size(),-1),pn(meshes.size(),-1),pj(meshes.size(),-1),pw(meshes.size(),-1);
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];int mj=-1;bool bone=o.mesh==5;
  if(o.mesh<3||o.mesh>=6){int m=o.mesh;
   if(pa[m]<0){std::vector<float> P,N;auto&c=meshes[m].cpu;for(size_t j=0;j+5<c.size();j+=6){P.insert(P.end(),{c[j],c[j+1],c[j+2]});N.insert(N.end(),{c[j+3],c[j+4],c[j+5]});}
    pa[m]=acc(P,3,"VEC3",mm3(P));pn[m]=acc(N,3,"VEC3","");
    if(meshes[m].skinned){std::vector<unsigned short> Jv;std::vector<float> Wv;auto&sk=meshes[m].skin;
     for(size_t j=0;j+7<sk.size();j+=8){for(int q=0;q<4;q++)Jv.push_back((unsigned short)sk[j+q]);for(int q=0;q<4;q++)Wv.push_back(sk[j+4+q]);}
     int vi=view(Jv.data(),Jv.size()*2);accs+=fm("%s{\"bufferView\":%d,\"componentType\":5123,\"count\":%d,\"type\":\"VEC4\"}",na?",":"",vi,(int)Jv.size()/4);pj[m]=na++;pw[m]=acc(Wv,4,"VEC4","");}}
   mats+=fm("%s{\"pbrMetallicRoughness\":{\"baseColorFactor\":[%g,%g,%g,1],\"metallicFactor\":%g,\"roughnessFactor\":%g}}",nm?",":"",o.col.x,o.col.y,o.col.z,o.met,o.rou);
   std::string at=fm("\"POSITION\":%d,\"NORMAL\":%d",pa[m],pn[m]);if(pj[m]>=0)at+=fm(",\"JOINTS_0\":%d,\"WEIGHTS_0\":%d",pj[m],pw[m]);
   meshJ+=fm("%s{\"primitives\":[{\"attributes\":{%s},\"material\":%d}]}",nm?",":"",at.c_str(),nm);mj=nm++;}
  float q[4];eq(o.cur.r,q);std::string ch;
  for(int j=0;j<(int)objs.size();j++)if(objs[j].parent==i)ch+=fm("%s%d",ch.empty()?"":",",j);
  std::string n=fm("{\"name\":\"%s\",\"translation\":[%g,%g,%g],\"rotation\":[%g,%g,%g,%g],\"scale\":[%g,%g,%g]",o.nm,
   o.cur.p.x,o.cur.p.y,o.cur.p.z,q[0],q[1],q[2],q[3],o.cur.s.x,o.cur.s.y,o.cur.s.z);
  if(mj>=0)n+=fm(",\"mesh\":%d",mj);if(mj>=0&&o.skin>=0&&meshes[o.mesh].skinned)n+=fm(",\"skin\":%d",o.skin);if(bone)n+=fm(",\"extras\":{\"bone\":true,\"length\":%g}",o.len);
  if(!ch.empty())n+=",\"children\":["+ch+"]";n+="}";nodes+=(i?",":"")+n;
  if(o.parent<0)roots+=fm("%s%d",roots.empty()?"":",",i);}
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];if(o.k.empty())continue;std::vector<float> ti,tp,rq,sc;
  for(auto&k:o.k){ti.push_back(k.t);tp.insert(tp.end(),{k.x.p.x,k.x.p.y,k.x.p.z});float q[4];eq(k.x.r,q);rq.insert(rq.end(),{q[0],q[1],q[2],q[3]});sc.insert(sc.end(),{k.x.s.x,k.x.s.y,k.x.s.z});}
  int ai=acc(ti,1,"SCALAR",fm(",\"min\":[%g],\"max\":[%g]",ti.front(),ti.back()));
  int ao[3]={acc(tp,3,"VEC3",""),acc(rq,4,"VEC4",""),acc(sc,3,"VEC3","")};static const char*PN[3]={"translation","rotation","scale"};
  for(int c=0;c<3;c++){samp+=fm("%s{\"input\":%d,\"output\":%d,\"interpolation\":\"LINEAR\"}",ns?",":"",ai,ao[c]);
   chn+=fm("%s{\"sampler\":%d,\"target\":{\"node\":%d,\"path\":\"%s\"}}",ns?",":"",ns,i,PN[c]);ns++;}}
 std::string js="{\"asset\":{\"version\":\"2.0\",\"generator\":\"Nomad Animator\"},\"scene\":0,\"scenes\":[{\"nodes\":["+roots+"]}],\"nodes\":["+nodes+"],";
 std::string skinJ;
 for(size_t si=0;si<skins.size();si++){Skin&sk=skins[si];std::vector<float> ib;std::string jl;
  for(size_t k=0;k<sk.j.size();k++){const float*mp=sk.ibm[k].m;ib.insert(ib.end(),mp,mp+16);jl+=(k?",":"")+std::to_string(std::max(sk.j[k],0));}
  int ai=acc(ib,16,"MAT4","");skinJ+=(si?",":"")+std::string("{\"inverseBindMatrices\":")+std::to_string(ai)+",\"joints\":["+jl+"]}";}
 if(!skinJ.empty())js+="\"skins\":["+skinJ+"],";
 if(nm)js+="\"meshes\":["+meshJ+"],\"materials\":["+mats+"],";
 if(ns)js+="\"animations\":[{\"name\":\"Anim\",\"samplers\":["+samp+"],\"channels\":["+chn+"]}],";
 js+="\"accessors\":["+accs+"],\"bufferViews\":["+views+"],\"buffers\":[{\"byteLength\":"+std::to_string(bin.size())+",\"uri\":\"data:application/octet-stream;base64,"+b64(bin)+"\"}]}";
 fwrite(js.data(),1,js.size(),f);fclose(f);saved(path,fb);}
// ---------- icones, importacao glTF ----------
float gFlash[64]={};bool gImportOpen=false;int gPick=0;std::vector<std::string> gFiles;
void icon2(int id,float cx,float cy,float s,bool on){
 if(id>=3&&id<=6){icon(id,cx,cy,s,on);return;}
 const float c=.93f;
 if(id==0){rect(cx-s*.35f,cy-s,s*1.4f,s*1.4f,.55f,.55f,.6f,1,s*.12f);rect(cx-s,cy-s*.4f,s*1.4f,s*1.4f,c,c,c,1,s*.12f);}
 else if(id==1){rect(cx-s,cy-s,2*s,2*s,c,c,c,1,s);rect(cx-s*.5f,cy-s*.6f,s*.5f,s*.5f,.6f,.6f,.65f,1,s*.25f);}
 else if(id==2){rect(cx-s*1.1f,cy-s*.3f,s*2.2f,s*.6f,c,c,c,1,s*.12f);}
 else if(id==10){rect(cx-s*.12f,cy-s*.7f,s*.24f,s*1.4f,c,c,c);rect(cx-s*.4f,cy+s*.3f,s*.8f,s*.8f,c,c,c,1,s*.4f);rect(cx-s*.25f,cy-s,s*.5f,s*.5f,c,c,c,1,s*.25f);}
 else if(id==11||id==12){rect(cx-s*.35f,cy-s,s*.7f,s*.7f,c,c,c,1,s*.35f);rect(cx-s*.12f,cy-s*.35f,s*.24f,s*.6f,c,c,c);rect(cx-s*.35f,cy+s*.3f,s*.7f,s*.7f,c,c,c,1,s*.35f);
  if(id==12)rect(cx-s*.9f,cy-s*.12f,s*1.8f,s*.24f,1,.45f,.4f);}
 else if(id==8){if(playing){rect(cx-s*.7f,cy-s,s*.55f,2*s,c,c,c,1,s*.1f);rect(cx+s*.15f,cy-s,s*.55f,2*s,c,c,c,1,s*.1f);}
  else for(int i=0;i<8;i++){float h=2*s*(1-i/8.f);rect(cx-s*.7f+i*s*.2f,cy-h/2,s*.22f,h,c,c,c);}}
 else if(id==40){rect(cx-s*.7f,cy-s,s*1.4f,s*2.f,c,c,c,1,s*.15f);rect(cx-s*.45f,cy-s*.1f,s*.9f,s*.2f,.3f,.3f,.33f);rect(cx-s*.1f,cy-s*.45f,s*.2f,s*.9f,.3f,.3f,.33f);}
 else if(id==41){rect(cx-s,cy-s*.75f,s*.8f,s*.4f,c,c,c,1,s*.1f);rect(cx-s,cy-s*.4f,s*2.f,s*1.3f,c,c,c,1,s*.12f);}
 else if(id==42){rect(cx-s*.9f,cy-s*.9f,s*1.8f,s*1.8f,c,c,c,1,s*.15f);rect(cx-s*.55f,cy-s*.9f,s*1.1f,s*.6f,.3f,.3f,.33f,1,s*.06f);rect(cx-s*.5f,cy+s*.2f,s,s*.7f,.3f,.3f,.33f,1,s*.06f);}
 else if(id==9){rect(cx-s*.8f,cy-s,s*1.6f,s*.25f,c,c,c);rect(cx-s*.3f,cy-s*1.2f,s*.6f,s*.25f,c,c,c);rect(cx-s*.65f,cy-s*.65f,s*1.3f,s*1.7f,c,c,c,1,s*.15f);}}
// ---------- permissao "Acesso a todos os arquivos" (via JNI) ----------
android_app*gApp=nullptr;
bool filesGranted(){
 if(!gApp||!gApp->activity)return true;JavaVM*vm=gApp->activity->vm;JNIEnv*env=nullptr;
 if(vm->AttachCurrentThread(&env,nullptr)!=JNI_OK||!env)return true;
 bool ok=true;jclass ec=env->FindClass("android/os/Environment");
 if(ec){jmethodID m=env->GetStaticMethodID(ec,"isExternalStorageManager","()Z");
  if(m)ok=env->CallStaticBooleanMethod(ec,m)!=JNI_FALSE;}
 if(env->ExceptionCheck())env->ExceptionClear();
 vm->DetachCurrentThread();return ok;}
void openFilesSettings(){
 if(!gApp||!gApp->activity)return;JavaVM*vm=gApp->activity->vm;JNIEnv*env=nullptr;
 if(vm->AttachCurrentThread(&env,nullptr)!=JNI_OK||!env)return;
 jobject act=gApp->activity->clazz;
 auto go=[&](const char*action,bool withPkg)->bool{
  jclass ic=env->FindClass("android/content/Intent");if(!ic){env->ExceptionClear();return false;}
  jmethodID ct=env->GetMethodID(ic,"<init>","(Ljava/lang/String;)V");
  jobject it=env->NewObject(ic,ct,env->NewStringUTF(action));
  if(withPkg){jclass uc=env->FindClass("android/net/Uri");
   jmethodID pr=env->GetStaticMethodID(uc,"parse","(Ljava/lang/String;)Landroid/net/Uri;");
   jobject uri=env->CallStaticObjectMethod(uc,pr,env->NewStringUTF("package:com.nomad.animator"));
   jmethodID sd=env->GetMethodID(ic,"setData","(Landroid/net/Uri;)Landroid/content/Intent;");env->CallObjectMethod(it,sd,uri);}
  jclass ac=env->GetObjectClass(act);jmethodID sa=env->GetMethodID(ac,"startActivity","(Landroid/content/Intent;)V");
  env->CallVoidMethod(act,sa,it);
  if(env->ExceptionCheck()){env->ExceptionClear();return false;}return true;};
 if(!go("android.settings.MANAGE_APP_ALL_FILES_ACCESS_PERMISSION",true))go("android.settings.MANAGE_ALL_FILES_ACCESS_PERMISSION",false);
 vm->DetachCurrentThread();}
void needFiles(){toast("Ative Permitir gerenciar todos os arquivos e volte ao app");openFilesSettings();}
void importGLTF(const std::string&path);
// ZIPBEGIN
static uint32_t rd32(const unsigned char*q){return q[0]|(q[1]<<8)|(q[2]<<16)|((uint32_t)q[3]<<24);}
static uint32_t rd16(const unsigned char*q){return q[0]|(q[1]<<8);}
static void mkdirs(const std::string&path){for(size_t i=1;i<path.size();i++)if(path[i]=='/')mkdir(path.substr(0,i).c_str(),0755);}
std::string unzipModel(const std::string&zp){
 FILE*f=fopen(zp.c_str(),"rb");if(!f)return "";
 fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);if(sz<22){fclose(f);return "";}
 std::vector<unsigned char> z(sz);size_t rd=fread(z.data(),1,sz,f);fclose(f);if((long)rd!=sz)return "";
 long e=-1;for(long i=sz-22;i>=0&&i>=sz-22-65535;i--)if(rd32(&z[i])==0x06054b50){e=i;break;}
 if(e<0)return "";
 int n=(int)rd16(&z[e+10]);uint32_t p=rd32(&z[e+16]);
 std::string nm=zp;size_t sl=nm.rfind('/');if(sl!=std::string::npos)nm=nm.substr(sl+1);size_t dt=nm.rfind('.');if(dt!=std::string::npos)nm=nm.substr(0,dt);
 std::string out=std::string(gDir)+"/import_"+nm;mkdir(out.c_str(),0755);std::string found;
 for(int i=0;i<n;i++){if((long)p+46>sz||rd32(&z[p])!=0x02014b50)break;
  int method=(int)rd16(&z[p+10]);uint32_t csz=rd32(&z[p+20]),usz=rd32(&z[p+24]);uint32_t nl=rd16(&z[p+28]),el=rd16(&z[p+30]),cl=rd16(&z[p+32]),lo=rd32(&z[p+42]);
  if((long)(p+46+nl)>sz)break;std::string name((const char*)&z[p+46],nl);p+=46+nl+el+cl;
  std::string l=name;for(auto&c:l)c=(char)tolower((unsigned char)c);
  auto ends=[&](const char*x){size_t k=strlen(x);return l.size()>k&&l.compare(l.size()-k,k,x)==0;};
  bool isg=ends(".gltf")||ends(".glb");
  if(!(isg||ends(".bin"))||name.find("..")!=std::string::npos||name[0]=='/')continue;
  if((long)lo+30>sz||rd32(&z[lo])!=0x04034b50)continue;
  uint32_t ds=lo+30+rd16(&z[lo+26])+rd16(&z[lo+28]);if((long)ds+(long)csz>sz)continue;
  std::vector<unsigned char> o(usz?usz:1);
  if(method==0){if(csz!=usz)continue;memcpy(o.data(),&z[ds],usz);}
  else if(method==8){z_stream zs;memset(&zs,0,sizeof zs);if(inflateInit2(&zs,-MAX_WBITS)!=Z_OK)continue;
   zs.next_in=&z[ds];zs.avail_in=csz;zs.next_out=o.data();zs.avail_out=usz;int r=inflate(&zs,Z_FINISH);inflateEnd(&zs);if(r!=Z_STREAM_END)continue;}
  else continue;
  std::string fp=out+"/"+name;mkdirs(fp);FILE*w=fopen(fp.c_str(),"wb");if(!w)continue;fwrite(o.data(),1,usz,w);fclose(w);
  if(isg&&found.empty())found=fp;}
 return found;}
// ZIPEND
void importPath(const std::string&p){std::string l=p;for(auto&c:l)c=(char)tolower((unsigned char)c);
 if(l.size()>4&&l.compare(l.size()-4,4,".zip")==0){std::string g=unzipModel(p);if(g.empty()){toast("O zip nao tem .gltf/.glb");return;}importGLTF(g);}else importGLTF(p);}
void scanDir(const std::string&dp,int depth,std::vector<std::pair<time_t,std::string>>&v){DIR*d=opendir(dp.c_str());if(!d)return;
 while(dirent*e=readdir(d)){std::string n=e->d_name;if(n=="."||n=="..")continue;std::string pth=dp+"/"+n;struct stat st;if(stat(pth.c_str(),&st)!=0)continue;
  if(S_ISDIR(st.st_mode)){if(depth>0&&n.compare(0,7,"import_")!=0)scanDir(pth,depth-1,v);continue;}
  std::string l=n;for(auto&ch:l)ch=(char)tolower((unsigned char)ch);
  auto ends=[&](const char*x){size_t k=strlen(x);return l.size()>k&&l.compare(l.size()-k,k,x)==0;};
  if(gPick==0?(ends(".gltf")||ends(".glb")||ends(".zip")):ends(".mad"))v.push_back({st.st_mtime,pth});}
 closedir(d);}
void scanFiles(){gFiles.clear();std::vector<std::pair<time_t,std::string>> v;
 scanDir("/storage/emulated/0/Download",1,v);scanDir(gDir,1,v);
 std::sort(v.rbegin(),v.rend());for(size_t i=0;i<v.size()&&i<8;i++)gFiles.push_back(v[i].second);}
void importGLTF(const std::string&path){
 cgltf_options op;memset(&op,0,sizeof op);cgltf_data*d=nullptr;
 if(cgltf_parse_file(&op,path.c_str(),&d)!=cgltf_result_success){toast("Falha ao ler o arquivo");return;}
 if(cgltf_load_buffers(&op,d,path.c_str())!=cgltf_result_success){cgltf_free(d);toast("Falta o .bin: ele precisa estar na mesma pasta do .gltf");return;}
 std::vector<int> mi(d->meshes_count,-1);std::vector<V> mc(d->meshes_count,V{.8f,.8f,.8f});std::vector<float> mmt(d->meshes_count,0.f),mrg(d->meshes_count,.6f);
 for(size_t m=0;m<d->meshes_count;m++){std::vector<float> v;bool gotc=false;std::vector<float> sk;bool anySk=false;
  for(size_t pi=0;pi<d->meshes[m].primitives_count;pi++){cgltf_primitive&pr=d->meshes[m].primitives[pi];if(pr.type!=cgltf_primitive_type_triangles)continue;
   cgltf_accessor*pos=nullptr,*nor=nullptr,*jn=nullptr,*wt=nullptr;
   for(size_t a=0;a<pr.attributes_count;a++){if(pr.attributes[a].type==cgltf_attribute_type_position)pos=pr.attributes[a].data;else if(pr.attributes[a].type==cgltf_attribute_type_normal)nor=pr.attributes[a].data;else if(pr.attributes[a].type==cgltf_attribute_type_joints&&pr.attributes[a].index==0)jn=pr.attributes[a].data;else if(pr.attributes[a].type==cgltf_attribute_type_weights&&pr.attributes[a].index==0)wt=pr.attributes[a].data;}
   if(!pos)continue;if(jn&&wt)anySk=true;
   if(!gotc&&pr.material&&pr.material->has_pbr_metallic_roughness){const float*c=pr.material->pbr_metallic_roughness.base_color_factor;mc[m]=V{c[0],c[1],c[2]};mmt[m]=pr.material->pbr_metallic_roughness.metallic_factor;mrg[m]=pr.material->pbr_metallic_roughness.roughness_factor;gotc=true;}
   size_t cnt=pr.indices?pr.indices->count:pos->count;
   for(size_t i=0;i+2<cnt;i+=3){V P[3],N[3];float SK[3][8];
    for(int k=0;k<3;k++){size_t ix=pr.indices?cgltf_accessor_read_index(pr.indices,i+k):i+k;float f[4]={0,0,0,0};
     cgltf_accessor_read_float(pos,ix,f,3);P[k]=V{f[0],f[1],f[2]};
     if(nor){cgltf_accessor_read_float(nor,ix,f,3);N[k]=V{f[0],f[1],f[2]};}
     float jf[4]={0,0,0,0},wf[4]={1,0,0,0};
     if(jn&&wt){cgltf_accessor_read_float(jn,ix,jf,4);cgltf_accessor_read_float(wt,ix,wf,4);float sm=wf[0]+wf[1]+wf[2]+wf[3];
      if(sm<1e-6f){wf[0]=1;wf[1]=wf[2]=wf[3]=0;jf[0]=0;}else for(int q=0;q<4;q++){if(jf[q]>=64){wf[q]=0;jf[q]=0;}wf[q]/=sm;}}
     for(int q=0;q<4;q++){SK[k][q]=jf[q];SK[k][4+q]=wf[q];}}
    if(!nor){V fn=cross(P[1]-P[0],P[2]-P[0]);float l=sqrtf(dot(fn,fn));fn=l>1e-12f?fn*(1/l):V{0,1,0};N[0]=N[1]=N[2]=fn;}
    for(int k=0;k<3;k++){vtx(v,P[k],N[k]);sk.insert(sk.end(),SK[k],SK[k]+8);}}}
  if(v.empty())continue;
  Mesh mm=upload(v,GL_TRIANGLES);float r=0;for(size_t i=0;i+2<v.size();i+=6)r=std::max(r,sqrtf(v[i]*v[i]+v[i+1]*v[i+1]+v[i+2]*v[i+2]));
  mm.rad=r>0?r:1;if(anySk)attachSkin(mm,sk);meshes.push_back(mm);mi[m]=(int)meshes.size()-1;}
 int base=(int)objs.size();size_t nn=d->nodes_count;int sb=(int)skins.size();
 for(size_t i=0;i<nn;i++){cgltf_node*nd=&d->nodes[i];Obj o;int mid=nd->mesh?(int)(nd->mesh-d->meshes):-1;
  o.mesh=(mid>=0&&mi[mid]>=0)?mi[mid]:5;o.col=(o.mesh==5)?V{.85f,.85f,.65f}:mc[mid];if(o.mesh!=5){o.met=mmt[mid];o.rou=mrg[mid];}
  snprintf(o.nm,24,"%s",nd->name?nd->name:"Node");o.skin=nd->skin?sb+(int)(nd->skin-d->skins):-1;o.parent=nd->parent?base+(int)(nd->parent-d->nodes):-1;T&t=o.cur;
  if(nd->has_matrix){float m[16];cgltf_node_transform_local(nd,m);t.p=V{m[12],m[13],m[14]};
   float sx=sqrtf(m[0]*m[0]+m[1]*m[1]+m[2]*m[2]),sy=sqrtf(m[4]*m[4]+m[5]*m[5]+m[6]*m[6]),sz=sqrtf(m[8]*m[8]+m[9]*m[9]+m[10]*m[10]);
   if(sx>0&&sy>0&&sz>0){t.s=V{sx,sy,sz};t.r.y=asinf(std::clamp(-m[2]/sx,-1.f,1.f));t.r.x=atan2f(m[6]/sy,m[10]/sz);t.r.z=atan2f(m[1]/sx,m[0]/sx);}}
  else{if(nd->has_translation)t.p=V{nd->translation[0],nd->translation[1],nd->translation[2]};
   if(nd->has_scale)t.s=V{nd->scale[0],nd->scale[1],nd->scale[2]};
   if(nd->has_rotation){float x=nd->rotation[0],y=nd->rotation[1],z=nd->rotation[2],w=nd->rotation[3];
    t.r.y=asinf(std::clamp(2*(w*y-z*x),-1.f,1.f));t.r.x=atan2f(2*(w*x+y*z),1-2*(x*x+y*y));t.r.z=atan2f(2*(w*z+x*y),1-2*(y*y+z*z));}}
  if(o.mesh==5){o.len=.25f;for(size_t c=0;c<nd->children_count;c++){cgltf_node*ch=nd->children[c];
   if(ch->has_translation){V tv{ch->translation[0],ch->translation[1],ch->translation[2]};float l=sqrtf(dot(tv,tv));if(l>.01f){o.len=l;break;}}}}
  objs.push_back(o);}
 for(size_t si=0;si<d->skins_count;si++){cgltf_skin&cs=d->skins[si];Skin sk;
  for(size_t k=0;k<cs.joints_count;k++){sk.j.push_back(base+(int)(cs.joints[k]-d->nodes));M im=id();
   if(cs.inverse_bind_matrices){float f16[16];cgltf_accessor_read_float(cs.inverse_bind_matrices,k,f16,16);memcpy(im.m,f16,sizeof im.m);}sk.ibm.push_back(im);}
  sk.fz.assign(sk.j.size(),id());skins.push_back(sk);}
 if(nn){float R=0;for(size_t i=0;i<nn;i++){Obj&o=objs[base+i];if(o.mesh==5)continue;M w=worldM(base+(int)i);V c{w.m[12],w.m[13],w.m[14]};
   float sc=std::max({sqrtf(w.m[0]*w.m[0]+w.m[1]*w.m[1]+w.m[2]*w.m[2]),sqrtf(w.m[4]*w.m[4]+w.m[5]*w.m[5]+w.m[6]*w.m[6]),sqrtf(w.m[8]*w.m[8]+w.m[9]*w.m[9]+w.m[10]*w.m[10])});
   R=std::max(R,sqrtf(dot(c,c))+meshes[o.mesh].rad*sc);}
  if(R>1e-4f){float f=(R>6||R<1.5f)?3.f/R:1.f;if(f!=1.f)for(size_t i=0;i<nn;i++){Obj&o=objs[base+i];if(o.parent<0){o.cur.s=o.cur.s*f;o.cur.p=o.cur.p*f;}}}
  sel=base;}
 cgltf_free(d);toast(fm("Importado: %d objetos",(int)nn));}
// ---------- SSAO (meia resolucao) + render pbr ----------
bool gSSAO=false,gPostOK=false,gMsOK=false,gBones=true;float gAOs=.85f,gFps=0,gFAcc=0;int gFN=0,gHW=1,gHH=1;
GLuint gMsFbo=0,gMsC=0,gMsD=0,gFbo=0,gCT=0,gDT=0,gAoFbo=0,gAoT=0,gAoP=0,gCoP=0;
GLint uAD,uATH,uANF,uAR,uASZ,uCC,uCA,uCT,uCS;
float gSlX[3]={0,0,1},gSlW[3]={1,1,1};
void setSlider(int i,float x){float v=std::clamp((x-gSlX[i])/gSlW[i],0.f,1.f);if(i==2){gAOs=v;return;}if(sel<0)return;if(i==0)objs[sel].met=v;else objs[sel].rou=v;}
GLuint mkProg(const char*vs,const char*fs){GLuint p=glCreateProgram();glAttachShader(p,sh(GL_VERTEX_SHADER,vs));glAttachShader(p,sh(GL_FRAGMENT_SHADER,fs));glLinkProgram(p);return p;}
void initPost(){
 gHW=std::max(W/2,1);gHH=std::max(H/2,1);
 auto tex=[&](GLuint&t,GLint ifmt,int w,int h,GLenum fmt,GLenum ty,GLint filt){glGenTextures(1,&t);glBindTexture(GL_TEXTURE_2D,t);glTexImage2D(GL_TEXTURE_2D,0,ifmt,w,h,0,fmt,ty,nullptr);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,filt);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,filt);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);};
 tex(gCT,GL_RGBA8,W,H,GL_RGBA,GL_UNSIGNED_BYTE,GL_LINEAR);tex(gDT,GL_DEPTH_COMPONENT24,W,H,GL_DEPTH_COMPONENT,GL_UNSIGNED_INT,GL_NEAREST);tex(gAoT,GL_R8,gHW,gHH,GL_RED,GL_UNSIGNED_BYTE,GL_LINEAR);
 glGenFramebuffers(1,&gFbo);glBindFramebuffer(GL_FRAMEBUFFER,gFbo);
 glFramebufferTexture2D(GL_FRAMEBUFFER,GL_COLOR_ATTACHMENT0,GL_TEXTURE_2D,gCT,0);glFramebufferTexture2D(GL_FRAMEBUFFER,GL_DEPTH_ATTACHMENT,GL_TEXTURE_2D,gDT,0);
 bool ok=glCheckFramebufferStatus(GL_FRAMEBUFFER)==GL_FRAMEBUFFER_COMPLETE;
 glGenFramebuffers(1,&gAoFbo);glBindFramebuffer(GL_FRAMEBUFFER,gAoFbo);glFramebufferTexture2D(GL_FRAMEBUFFER,GL_COLOR_ATTACHMENT0,GL_TEXTURE_2D,gAoT,0);
 ok=ok&&glCheckFramebufferStatus(GL_FRAMEBUFFER)==GL_FRAMEBUFFER_COMPLETE;
 GLint ms=0;glGetIntegerv(GL_MAX_SAMPLES,&ms);ms=std::min(ms,4);gMsOK=false;
 if(ms>=2){glGenRenderbuffers(1,&gMsC);glBindRenderbuffer(GL_RENDERBUFFER,gMsC);glRenderbufferStorageMultisample(GL_RENDERBUFFER,ms,GL_RGBA8,W,H);
  glGenRenderbuffers(1,&gMsD);glBindRenderbuffer(GL_RENDERBUFFER,gMsD);glRenderbufferStorageMultisample(GL_RENDERBUFFER,ms,GL_DEPTH_COMPONENT24,W,H);
  glGenFramebuffers(1,&gMsFbo);glBindFramebuffer(GL_FRAMEBUFFER,gMsFbo);
  glFramebufferRenderbuffer(GL_FRAMEBUFFER,GL_COLOR_ATTACHMENT0,GL_RENDERBUFFER,gMsC);glFramebufferRenderbuffer(GL_FRAMEBUFFER,GL_DEPTH_ATTACHMENT,GL_RENDERBUFFER,gMsD);
  gMsOK=glCheckFramebufferStatus(GL_FRAMEBUFFER)==GL_FRAMEBUFFER_COMPLETE;}
 glBindFramebuffer(GL_FRAMEBUFFER,0);gPostOK=ok;
 const char*qv="#version 300 es\nlayout(location=0) in vec3 aP; out vec2 vUV; void main(){vUV=aP.xy;gl_Position=vec4(aP.xy*2.0-1.0,0.0,1.0);}";
 const char*af=R"(#version 300 es
precision highp float; in vec2 vUV; uniform sampler2D uD; uniform vec2 uTH; uniform vec2 uNF; uniform vec2 uSz; uniform float uR; out vec4 o;
const float bay[16]=float[16](0.,8.,2.,10.,12.,4.,14.,6.,3.,11.,1.,9.,15.,7.,13.,5.);
float lin(float d){float z=d*2.0-1.0;return 2.0*uNF.x*uNF.y/(uNF.y+uNF.x-z*(uNF.y-uNF.x));}
vec3 vp(ivec2 p){float e=lin(texelFetch(uD,p,0).r);vec2 uv=(vec2(p)+0.5)/uSz;return vec3((uv*2.0-1.0)*uTH*e,-e);}
void main(){ivec2 p=ivec2(gl_FragCoord.xy*2.0);if(texelFetch(uD,p,0).r>=0.99999){o=vec4(1.0);return;}
 vec3 P=vp(p),Pl=vp(p-ivec2(1,0)),Pr=vp(p+ivec2(1,0)),Pd=vp(p-ivec2(0,1)),Pu=vp(p+ivec2(0,1));
 vec3 dx=abs(Pr.z-P.z)<abs(P.z-Pl.z)?Pr-P:P-Pl;vec3 dy=abs(Pu.z-P.z)<abs(P.z-Pd.z)?Pu-P:P-Pd;
 vec3 N=normalize(cross(dx,dy));if(dot(N,-P)<0.0)N=-N;
 int bi=int(mod(gl_FragCoord.x,4.0))+4*int(mod(gl_FragCoord.y,4.0));float rot=(bay[bi]+0.5)/16.0*6.2831853;
 vec3 T=normalize(cross(N,abs(N.y)<0.9?vec3(0.0,1.0,0.0):vec3(1.0,0.0,0.0)));vec3 B=cross(N,T);
 vec3 P0=P+N*0.03*uR;float occ=0.0;
 for(int i=0;i<12;i++){float t=(float(i)+0.5)/12.0;float ph=float(i)*2.39996+rot;float s=sqrt(t);
  vec3 k=vec3(cos(ph)*s,sin(ph)*s,sqrt(1.0-t));k*=mix(0.2,1.0,t*t);
  vec3 sp=P0+(T*k.x+B*k.y+N*k.z)*uR;if(sp.z>-0.01)continue;
  vec2 uv=sp.xy/(-sp.z*uTH)*0.5+0.5;if(uv.x<0.0||uv.y<0.0||uv.x>1.0||uv.y>1.0)continue;
  float sd=lin(texelFetch(uD,min(ivec2(uv*uSz),ivec2(uSz)-1),0).r);
  float rc=smoothstep(0.0,1.0,uR/abs(-P.z-sd));occ+=(sd<-sp.z-0.06*uR?1.0:0.0)*rc;}
 o=vec4(1.0-occ/12.0);})";
 const char*cf=R"(#version 300 es
precision highp float; in vec2 vUV; uniform sampler2D uCol; uniform sampler2D uAO; uniform vec2 uTx; uniform float uStr; out vec4 o;
void main(){vec4 c=texture(uCol,vUV);vec2 q0=floor(vUV/uTx+0.5);
 float a=(texture(uAO,(q0+vec2(-1.0,-1.0))*uTx).r+texture(uAO,(q0+vec2(1.0,-1.0))*uTx).r+texture(uAO,(q0+vec2(-1.0,1.0))*uTx).r+texture(uAO,(q0+vec2(1.0,1.0))*uTx).r)*0.25;
 o=vec4(c.rgb*mix(1.0,a,uStr),1.0);})";
 gAoP=mkProg(qv,af);gCoP=mkProg(qv,cf);
 uAD=glGetUniformLocation(gAoP,"uD");uATH=glGetUniformLocation(gAoP,"uTH");uANF=glGetUniformLocation(gAoP,"uNF");uAR=glGetUniformLocation(gAoP,"uR");uASZ=glGetUniformLocation(gAoP,"uSz");
 uCC=glGetUniformLocation(gCoP,"uCol");uCA=glGetUniformLocation(gCoP,"uAO");uCT=glGetUniformLocation(gCoP,"uTx");uCS=glGetUniformLocation(gCoP,"uStr");
 glUseProgram(gProg);}
void runPost(){
 if(gMsOK){glBindFramebuffer(GL_READ_FRAMEBUFFER,gMsFbo);glBindFramebuffer(GL_DRAW_FRAMEBUFFER,gFbo);
  glBlitFramebuffer(0,0,W,H,0,0,W,H,GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT,GL_NEAREST);}
 glDisable(GL_DEPTH_TEST);glDisable(GL_BLEND);glBindVertexArray(meshes[3].vao);
 glBindFramebuffer(GL_FRAMEBUFFER,gAoFbo);glViewport(0,0,gHW,gHH);glUseProgram(gAoP);
 glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gDT);glUniform1i(uAD,0);
 float th=tanf(FOV/2);glUniform2f(uATH,th*(float)W/H,th);glUniform2f(uANF,.1f,100.f);glUniform1f(uAR,.55f);glUniform2f(uASZ,(float)W,(float)H);glDrawArrays(GL_TRIANGLES,0,6);
 glBindFramebuffer(GL_FRAMEBUFFER,0);glViewport(0,0,W,H);glUseProgram(gCoP);
 glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gCT);glActiveTexture(GL_TEXTURE1);glBindTexture(GL_TEXTURE_2D,gAoT);
 glUniform1i(uCC,0);glUniform1i(uCA,1);glUniform2f(uCT,1.f/gHW,1.f/gHH);glUniform1f(uCS,gAOs);glDrawArrays(GL_TRIANGLES,0,6);
 glActiveTexture(GL_TEXTURE0);glEnable(GL_BLEND);glUseProgram(gProg);}
const char*MCCS=R"MC(#version 310 es
precision highp float;precision highp int;
layout(local_size_x=8,local_size_y=8,local_size_z=1) in;
layout(rgba32f,binding=0) writeonly uniform highp image2D uOut;
uniform highp sampler2D uPrev;
layout(rgba16f,binding=1) writeonly uniform highp image2D uAovOut;
uniform highp sampler2D uAovPrev;
uniform int uN;
layout(std430,binding=0) readonly buffer NB{vec4 nd[];};
layout(std430,binding=1) readonly buffer TB{vec4 tr[];};
uniform ivec2 uSize;uniform int uOffY,uFirst,uFrame,uBounces;
uniform vec3 uCam,uF,uR,uU;uniform vec2 uTH;uniform vec3 uSunD,uSunC;uniform float uSunCos;
uint rs;
uint pcg(uint v){uint s=v*747796405u+2891336453u;uint w=((s>>((s>>28u)+4u))^s)*277803737u;return (w>>22u)^w;}
float rnd(){rs=pcg(rs);return float(rs)*(1.0/4294967296.0);}
const float PI=3.14159265;
vec3 sky(vec3 d){return mix(vec3(.30,.28,.26),vec3(.42,.52,.78),clamp(d.y*.5+.5,0.,1.))*.9;}
bool hit(vec3 o,vec3 d,bool any,out float th,out int ti,out vec2 buv){
 th=1e30;ti=-1;buv=vec2(0.0);vec3 id=1.0/mix(d,vec3(1e-9),lessThan(abs(d),vec3(1e-9)));
 int st[32];int sp=0;st[sp++]=0;
 while(sp>0){int n=st[--sp];vec4 a=nd[2*n],b=nd[2*n+1];
  vec3 t0=(a.xyz-o)*id,t1=(b.xyz-o)*id;vec3 tn=min(t0,t1),tf=max(t0,t1);
  float tmin=max(max(tn.x,tn.y),max(tn.z,0.0)),tmx=min(min(tf.x,tf.y),min(tf.z,th));
  if(tmin>tmx)continue;
  int cnt=floatBitsToInt(b.w),lf=floatBitsToInt(a.w);
  if(cnt>0){for(int i=0;i<cnt;i++){int t=lf+i;vec3 p0=tr[8*t].xyz,p1=tr[8*t+1].xyz,p2=tr[8*t+2].xyz;
    vec3 e1=p1-p0,e2=p2-p0,pv=cross(d,e2);float det=dot(e1,pv);if(abs(det)<1e-12)continue;float inv=1.0/det;
    vec3 tv=o-p0;float u=dot(tv,pv)*inv;if(u<0.0||u>1.0)continue;vec3 qv=cross(tv,e1);float v=dot(d,qv)*inv;if(v<0.0||u+v>1.0)continue;
    float tt=dot(e2,qv)*inv;if(tt>1e-4&&tt<th){th=tt;ti=t;buv=vec2(u,v);if(any)return true;}}}
  else{st[sp++]=lf;st[sp++]=n+1;}}
 return ti>=0;}
vec3 brdf(vec3 L,vec3 N,vec3 V,vec3 alb,float met,float rou,vec3 F0){
 vec3 H=normalize(L+V);float a=rou*rou,a2=a*a;float NL=max(dot(N,L),1e-4),NV=max(dot(N,V),1e-3),NH=max(dot(N,H),0.0),VH=max(dot(V,H),0.0);
 float dd=NH*NH*(a2-1.0)+1.0;float D=a2/(PI*dd*dd+1e-7);float k=(rou+1.0)*(rou+1.0)/8.0;
 float G=(NL/(NL*(1.0-k)+k))*(NV/(NV*(1.0-k)+k));vec3 F=F0+(1.0-F0)*pow(1.0-VH,5.0);
 return (1.0-F)*(1.0-met)*alb/PI+D*G*F/(4.0*NV*NL);}
void basis(vec3 N,out vec3 T,out vec3 B){T=normalize(cross(N,abs(N.y)<0.99?vec3(0.0,1.0,0.0):vec3(1.0,0.0,0.0)));B=cross(N,T);}
void main(){
 ivec2 px=ivec2(gl_GlobalInvocationID.xy)+ivec2(0,uOffY);if(px.x>=uSize.x||px.y>=uSize.y)return;
 rs=pcg(uint(px.x)*1973u+uint(px.y)*9277u+uint(uFrame)*26699u+1u);
 vec2 uv=(vec2(px)+vec2(rnd(),rnd()))/vec2(uSize)*2.0-1.0;
 vec3 rd=normalize(uF+uR*(uv.x*uTH.x)+uU*(uv.y*uTH.y));vec3 ro=uCam;
 vec3 Lo=vec3(0.0),T=vec3(1.0);vec3 aN=vec3(0.0);float aD=1e4;
 for(int b=0;b<uBounces;b++){
  float th;int ti;vec2 bu;
  if(!hit(ro,rd,false,th,ti,bu)){Lo+=T*sky(rd);break;}
  vec3 n0=tr[8*ti+3].xyz,n1=tr[8*ti+4].xyz,n2=tr[8*ti+5].xyz;
  vec3 N=normalize(n0*(1.0-bu.x-bu.y)+n1*bu.x+n2*bu.y);
  vec4 m1=tr[8*ti+6],m2=tr[8*ti+7];
  vec3 alb=m1.rgb;float met=m1.a,rou=clamp(m2.x,0.05,1.0);vec3 F0=mix(vec3(0.04),alb,met);
  vec3 V=-rd;if(dot(N,V)<0.0)N=-N;if(b==0){aN=N;aD=th;}vec3 P=ro+rd*th+N*0.002;
  vec3 TT,BB;basis(uSunD,TT,BB);float cz=1.0-rnd()*(1.0-uSunCos),sz=sqrt(max(1.0-cz*cz,0.0)),ph=2.0*PI*rnd();
  vec3 sd=normalize(TT*(sz*cos(ph))+BB*(sz*sin(ph))+uSunD*cz);float NLs=dot(N,sd);
  if(NLs>0.0){float t2;int i2;vec2 b2;if(!hit(P,sd,true,t2,i2,b2))Lo+=T*brdf(sd,N,V,alb,met,rou,F0)*uSunC*NLs;}
  float a=rou*rou,a2=a*a,ps=mix(0.5,1.0,met);vec3 Ld;vec3 T0,B0;basis(N,T0,B0);
  if(rnd()<ps){float u1=rnd(),u2=rnd();float ct=sqrt((1.0-u2)/(1.0+(a2-1.0)*u2)),st=sqrt(max(1.0-ct*ct,0.0)),p2=2.0*PI*u1;
   vec3 H=normalize(T0*(st*cos(p2))+B0*(st*sin(p2))+N*ct);Ld=reflect(-V,H);}
  else{float u1=rnd(),u2=rnd();float r=sqrt(u1),p2=2.0*PI*u2;Ld=normalize(T0*(r*cos(p2))+B0*(r*sin(p2))+N*sqrt(max(1.0-u1,0.0)));}
  float NL=dot(N,Ld);if(NL<=0.0)break;
  vec3 H2=normalize(Ld+V);float NH=max(dot(N,H2),0.0),VH=max(dot(V,H2),1e-4);
  float dd=NH*NH*(a2-1.0)+1.0,D=a2/(PI*dd*dd+1e-7);
  float pdf=(1.0-ps)*NL/PI+ps*D*NH/(4.0*VH);
  T*=brdf(Ld,N,V,alb,met,rou,F0)*NL/max(pdf,1e-5);
  if(b>=2){float q=clamp(max(T.r,max(T.g,T.b)),0.05,0.95);if(rnd()>q)break;T/=q;}
  ro=P;rd=Ld;}
 vec4 prev=uFirst==1?vec4(0.0):texelFetch(uPrev,px,0);
 imageStore(uOut,px,prev+vec4(min(Lo,vec3(20.0)),1.0));
 vec4 av=vec4(aN,aD);vec4 pa=uFirst==1?av:texelFetch(uAovPrev,px,0);
 imageStore(uAovOut,px,vec4(pa.rgb+(av.rgb-pa.rgb)/float(uN),pa.a+(av.a-pa.a)/float(uN)));}
)MC";
const char*DNCS=R"MC(#version 310 es
precision highp float;precision highp int;
layout(local_size_x=8,local_size_y=8,local_size_z=1) in;
layout(rgba16f,binding=0) writeonly uniform highp image2D uOut;
uniform highp sampler2D uSrc;uniform highp sampler2D uAov;
uniform ivec2 uSize;uniform int uStep,uIter0;uniform float uPhiC;
vec3 col(ivec2 p){vec4 c=texelFetch(uSrc,p,0);return uIter0==1?(c.a>0.0?c.rgb/c.a:vec3(0.0)):c.rgb;}
float lum(vec3 c){return dot(c,vec3(0.2126,0.7152,0.0722));}
void main(){ivec2 p=ivec2(gl_GlobalInvocationID.xy);if(p.x>=uSize.x||p.y>=uSize.y)return;
 vec4 ap=texelFetch(uAov,p,0);vec3 cp=col(p);float lp=lum(cp);vec3 sum=vec3(0.0);float ws=0.0;
 for(int j=-1;j<=1;j++)for(int i=-1;i<=1;i++){
  ivec2 q=clamp(p+ivec2(i,j)*uStep,ivec2(0),uSize-1);float k=(i==0?2.0:1.0)*(j==0?2.0:1.0);
  vec4 aq=texelFetch(uAov,q,0);vec3 cq=col(q);
  float wn=pow(max(dot(ap.xyz,aq.xyz),0.0),24.0);
  float wd=exp(-abs(ap.w-aq.w)/(0.03*ap.w+0.02*float(uStep)*ap.w+1e-3));
  float wc=exp(-abs(lp-lum(cq))/uPhiC);
  float w=(i==0&&j==0)?k:k*wn*wd*wc;sum+=cq*w;ws+=w;}
 imageStore(uOut,p,vec4(sum/max(ws,1e-6),1.0));}
)MC";
const char*MCTM=R"MC(#version 300 es
precision highp float; in vec2 vUV; uniform sampler2D uAcc; uniform ivec2 uSz; out vec4 o;
vec3 fetchC(ivec2 p){p=clamp(p,ivec2(0),uSz-1);vec4 a=texelFetch(uAcc,p,0);return a.a>0.0?a.rgb/a.a:vec3(0.0);}
void main(){vec2 p=vUV*vec2(uSz)-0.5;ivec2 i0=ivec2(floor(p));vec2 f=fract(p);
 vec3 c=mix(mix(fetchC(i0),fetchC(i0+ivec2(1,0)),f.x),mix(fetchC(i0+ivec2(0,1)),fetchC(i0+ivec2(1,1)),f.x),f.y);
 c=c*(2.51*c+0.03)/(c*(2.43*c+0.59)+0.14);o=vec4(pow(clamp(c,0.0,1.0),vec3(1.0/2.2)),1.0);}
)MC";
// ---------- Monte Carlo (preview) e path tracing (render final) ----------
struct TriD{V p[3],n[3];V col;float met=0,rou=.5f;};struct BN{V mn,mx;int lf=0,cnt=0;};
std::vector<TriD> gTD;std::vector<int> gOrd;std::vector<V> gCen;std::vector<BN> gBN;
bool gMcOK=false,gMcPrev=false,gMcFinal=false,gMcGround=true,gMcHaveCam=false;
int gMcSpp=64,gMcSamples=0,gMcRow=0,gMcRows=24,gMcW=0,gMcH=0,gMcCur=0,gMcFrame=0;
GLuint gMcTex[2]={0,0},gMcProg=0,gMcTm=0,gMcNB=0,gMcTB=0,gMcOutF=0,gMcOutT=0;
GLuint gMcAov[2]={0,0},gMcDnT[2]={0,0},gDnProg=0;bool gMcDn=true,gMcDnOK=false,gDnDirty=false;int gMcDnRes=0;GLint dnSrc,dnAov,dnSz,dnStep,dnI0,dnPhi,mcAovPrev,mcN;
GLint mcSz,mcOff,mcFirst,mcFr,mcBn,mcCam,mcF,mcR,mcU,mcTH,mcSD,mcSC,mcSCos,mcPrv,tmAcc,tmSz;
double gSigS=-1,gSigC=-1,gMcLast=0;float gDt=.016f;V gCE,gCF,gCR,gCU;
double nowSec(){timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
V vmin(V a,V b){return V{std::min(a.x,b.x),std::min(a.y,b.y),std::min(a.z,b.z)};}
V vmax(V a,V b){return V{std::max(a.x,b.x),std::max(a.y,b.y),std::max(a.z,b.z)};}
V xf(const M&m,V p){return V{m.m[0]*p.x+m.m[4]*p.y+m.m[8]*p.z+m.m[12],m.m[1]*p.x+m.m[5]*p.y+m.m[9]*p.z+m.m[13],m.m[2]*p.x+m.m[6]*p.y+m.m[10]*p.z+m.m[14]};}
V xn(const M&m,V p){return V{m.m[0]*p.x+m.m[4]*p.y+m.m[8]*p.z,m.m[1]*p.x+m.m[5]*p.y+m.m[9]*p.z,m.m[2]*p.x+m.m[6]*p.y+m.m[10]*p.z};}
void mcReset(){gMcSamples=0;gMcRow=0;gMcFrame=0;gMcDnOK=false;}
void gatherTris(){gTD.clear();std::vector<std::vector<M>> JS(skins.size());
 for(size_t s2=0;s2<skins.size();s2++){Skin&sk=skins[s2];JS[s2].resize(sk.j.size());
  for(size_t k=0;k<sk.j.size();k++){M jw=sk.j[k]>=0?worldM(sk.j[k]):(k<sk.fz.size()?sk.fz[k]:id());JS[s2][k]=mul(jw,sk.ibm[k]);}}
 for(int i=0;i<(int)objs.size()&&gTD.size()<150000;i++){Obj&o=objs[i];if(o.mesh==5)continue;Mesh&m=meshes[o.mesh];if(m.cpu.empty())continue;
  M w=worldM(i);bool sk=o.skin>=0&&o.skin<(int)skins.size()&&m.skinned;V col{powf(o.col.x,2.2f),powf(o.col.y,2.2f),powf(o.col.z,2.2f)};
  for(size_t v=0;v+17<m.cpu.size();v+=18){TriD t;t.col=col;t.met=o.met;t.rou=o.rou;
   for(int k=0;k<3;k++){const float*c=&m.cpu[v+6*k];V pp{c[0],c[1],c[2]},nn{c[3],c[4],c[5]};
    if(sk){const float*sw=&m.skin[(v/6+k)*8];V ap,an;for(int q=0;q<4;q++){float wq=sw[4+q];if(wq<=0)continue;int ji=(int)sw[q];if(ji>=(int)JS[o.skin].size())continue;
      ap=ap+xf(JS[o.skin][ji],pp)*wq;an=an+xn(JS[o.skin][ji],nn)*wq;}pp=ap;nn=an;}
    else{pp=xf(w,pp);nn=xn(w,nn);}
    float l=sqrtf(dot(nn,nn));t.p[k]=pp;t.n[k]=l>1e-8f?nn*(1/l):V{0,1,0};}
   gTD.push_back(t);}}
 if(gMcGround){TriD a;a.col=V{.25f,.25f,.25f};a.rou=.85f;V q[4]={{-60,-.002f,-60},{60,-.002f,-60},{60,-.002f,60},{-60,-.002f,60}};
  for(int k=0;k<3;k++)a.n[k]=V{0,1,0};TriD b=a;a.p[0]=q[0];a.p[1]=q[2];a.p[2]=q[1];b.p[0]=q[0];b.p[1]=q[3];b.p[2]=q[2];gTD.push_back(a);gTD.push_back(b);}
 if(gTD.empty()){TriD t;t.p[0]=V{1e6f,1e6f,1e6f};t.p[1]=V{1e6f+1,1e6f,1e6f};t.p[2]=V{1e6f,1e6f+1,1e6f};gTD.push_back(t);}}
int bvhRec(int b,int e){int id_=(int)gBN.size();gBN.push_back(BN());BN n;n.mn=V{1e30f,1e30f,1e30f};n.mx=V{-1e30f,-1e30f,-1e30f};V cmn=n.mn,cmx=n.mx;
 for(int i=b;i<e;i++){TriD&t=gTD[gOrd[i]];for(int k=0;k<3;k++){n.mn=vmin(n.mn,t.p[k]);n.mx=vmax(n.mx,t.p[k]);}cmn=vmin(cmn,gCen[gOrd[i]]);cmx=vmax(cmx,gCen[gOrd[i]]);}
 if(e-b<=4){n.lf=b;n.cnt=e-b;gBN[id_]=n;return id_;}
 V ex=cmx-cmn;int ax=(ex.x>ex.y&&ex.x>ex.z)?0:(ex.y>ex.z?1:2);int m=(b+e)/2;
 std::nth_element(gOrd.begin()+b,gOrd.begin()+m,gOrd.begin()+e,[&](int a,int c){return (&gCen[a].x)[ax]<(&gCen[c].x)[ax];});
 bvhRec(b,m);int r=bvhRec(m,e);n.lf=r;n.cnt=0;gBN[id_]=n;return id_;}
void mcBuild(){gatherTris();int n=(int)gTD.size();gOrd.resize(n);gCen.resize(n);
 for(int i=0;i<n;i++){gOrd[i]=i;gCen[i]=(gTD[i].p[0]+gTD[i].p[1]+gTD[i].p[2])*(1.f/3);}
 gBN.clear();bvhRec(0,n);std::vector<float> nd,tr;
 auto bits=[](int v){float f;memcpy(&f,&v,4);return f;};
 for(auto&b:gBN)nd.insert(nd.end(),{b.mn.x,b.mn.y,b.mn.z,bits(b.lf),b.mx.x,b.mx.y,b.mx.z,bits(b.cnt)});
 for(int i=0;i<n;i++){TriD&t=gTD[gOrd[i]];for(int k=0;k<3;k++)tr.insert(tr.end(),{t.p[k].x,t.p[k].y,t.p[k].z,0.f});
  for(int k=0;k<3;k++)tr.insert(tr.end(),{t.n[k].x,t.n[k].y,t.n[k].z,0.f});tr.insert(tr.end(),{t.col.x,t.col.y,t.col.z,t.met,t.rou,0.f,0.f,0.f});}
 glBindBuffer(GL_SHADER_STORAGE_BUFFER,gMcNB);glBufferData(GL_SHADER_STORAGE_BUFFER,nd.size()*4,nd.data(),GL_DYNAMIC_DRAW);
 glBindBuffer(GL_SHADER_STORAGE_BUFFER,gMcTB);glBufferData(GL_SHADER_STORAGE_BUFFER,tr.size()*4,tr.data(),GL_DYNAMIC_DRAW);}
void initMC(){gMcOK=false;gMcW=gMcH=0;gMcTex[0]=gMcTex[1]=0;gMcOutF=gMcOutT=0;gMcAov[0]=gMcAov[1]=gMcDnT[0]=gMcDnT[1]=0;gMcDnOK=false;gMcSamples=0;gSigS=gSigC=-1;gMcHaveCam=false;
 GLint ma=0,mi=0;glGetIntegerv(GL_MAJOR_VERSION,&ma);glGetIntegerv(GL_MINOR_VERSION,&mi);if(ma<3||(ma==3&&mi<1))return;
 GLuint p=glCreateProgram();glAttachShader(p,sh(GL_COMPUTE_SHADER,MCCS));glLinkProgram(p);GLint ok=0;glGetProgramiv(p,GL_LINK_STATUS,&ok);
 if(!ok){char b[512];glGetProgramInfoLog(p,512,0,b);__android_log_print(ANDROID_LOG_ERROR,"NA","MC: %s",b);return;}
 gMcProg=p;mcSz=glGetUniformLocation(p,"uSize");mcOff=glGetUniformLocation(p,"uOffY");mcFirst=glGetUniformLocation(p,"uFirst");mcFr=glGetUniformLocation(p,"uFrame");
 mcBn=glGetUniformLocation(p,"uBounces");mcCam=glGetUniformLocation(p,"uCam");mcF=glGetUniformLocation(p,"uF");mcR=glGetUniformLocation(p,"uR");mcU=glGetUniformLocation(p,"uU");
 mcTH=glGetUniformLocation(p,"uTH");mcSD=glGetUniformLocation(p,"uSunD");mcSC=glGetUniformLocation(p,"uSunC");mcSCos=glGetUniformLocation(p,"uSunCos");mcPrv=glGetUniformLocation(p,"uPrev");
 const char*qv="#version 300 es\nlayout(location=0) in vec3 aP; out vec2 vUV; void main(){vUV=aP.xy;gl_Position=vec4(aP.xy*2.0-1.0,0.0,1.0);}";
 gMcTm=mkProg(qv,MCTM);tmAcc=glGetUniformLocation(gMcTm,"uAcc");tmSz=glGetUniformLocation(gMcTm,"uSz");mcAovPrev=glGetUniformLocation(p,"uAovPrev");mcN=glGetUniformLocation(p,"uN");
 {GLuint dp=glCreateProgram();glAttachShader(dp,sh(GL_COMPUTE_SHADER,DNCS));glLinkProgram(dp);GLint ok2=0;glGetProgramiv(dp,GL_LINK_STATUS,&ok2);
  if(ok2){gDnProg=dp;dnSrc=glGetUniformLocation(dp,"uSrc");dnAov=glGetUniformLocation(dp,"uAov");dnSz=glGetUniformLocation(dp,"uSize");
   dnStep=glGetUniformLocation(dp,"uStep");dnI0=glGetUniformLocation(dp,"uIter0");dnPhi=glGetUniformLocation(dp,"uPhiC");}else gDnProg=0;}
 glGenBuffers(1,&gMcNB);glGenBuffers(1,&gMcTB);glUseProgram(gProg);gMcOK=true;}
void mcResize(int w,int h){
 if(gMcTex[0]){glDeleteTextures(2,gMcTex);glDeleteTextures(2,gMcAov);glDeleteTextures(2,gMcDnT);glDeleteTextures(1,&gMcOutT);glDeleteFramebuffers(1,&gMcOutF);}
 glGenTextures(2,gMcTex);
 for(int i=0;i<2;i++){glBindTexture(GL_TEXTURE_2D,gMcTex[i]);glTexStorage2D(GL_TEXTURE_2D,1,GL_RGBA32F,w,h);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);}
 glGenTextures(2,gMcAov);glGenTextures(2,gMcDnT);
 for(int i=0;i<4;i++){glBindTexture(GL_TEXTURE_2D,i<2?gMcAov[i]:gMcDnT[i-2]);glTexStorage2D(GL_TEXTURE_2D,1,GL_RGBA16F,w,h);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
  glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);}
 glGenTextures(1,&gMcOutT);glBindTexture(GL_TEXTURE_2D,gMcOutT);glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA8,w,h,0,GL_RGBA,GL_UNSIGNED_BYTE,nullptr);
 glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_LINEAR);
 glGenFramebuffers(1,&gMcOutF);glBindFramebuffer(GL_FRAMEBUFFER,gMcOutF);glFramebufferTexture2D(GL_FRAMEBUFFER,GL_COLOR_ATTACHMENT0,GL_TEXTURE_2D,gMcOutT,0);
 glBindFramebuffer(GL_FRAMEBUFFER,0);gMcW=w;gMcH=h;gMcCur=0;mcReset();}
double sigScene(){double s2=0;for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];M w=worldM(i);for(int k=0;k<16;k++)s2+=w.m[k]*(k+1)*(i+1)*.37;
  s2+=(o.col.x+o.col.y*2+o.col.z*3+o.met*5+o.rou*7+o.len)*(i+1);}return s2+objs.size()*1000.0+(gMcGround?7:0);}
double sigCam(){return yaw*3.1+pitch*7.3+cd*11.7+tgt.x+tgt.y*2+tgt.z*3;}
bool mcShow(){return gMcOK&&(gMcPrev||gMcFinal)&&gMcSamples>0&&gMcTex[0];}
void mcStep(){
 if(!gMcOK||!(gMcPrev||gMcFinal))return;
 int tw_,th_;if(gMcFinal){float sc=std::min(1.f,1920.f/W);tw_=(int)(W*sc);th_=(int)(H*sc);}else{tw_=std::max(W/2,64);th_=std::max(H/2,64);}
 if(tw_!=gMcW||th_!=gMcH){mcResize(tw_,th_);gSigS=-1;gMcHaveCam=false;}
 double now=nowSec();V e=camEye();V f=norm(tgt-e),r=norm(cross(f,V{0,1,0})),u=cross(r,f);
 if(gMcFinal){if(!gMcHaveCam){mcBuild();gCE=e;gCF=f;gCR=r;gCU=u;mcReset();gMcHaveCam=true;}e=gCE;f=gCF;r=gCR;u=gCU;}
 else{double ss=sigScene(),sc2=sigCam();bool rs=false;
  if(ss!=gSigS&&now-gMcLast>.15){mcBuild();gSigS=ss;gMcLast=now;rs=true;}
  if(sc2!=gSigC){gSigC=sc2;rs=true;}if(rs)mcReset();}
 int cap=gMcFinal?gMcSpp:128;if(gMcSamples>=cap)return;
 if(gDt>.045f)gMcRows=std::max(8,gMcRows*3/4);else if(gDt<.028f)gMcRows=std::min(gMcH,gMcRows*5/4+1);
 int rows=std::min(gMcRows,gMcH-gMcRow);
 glUseProgram(gMcProg);glBindBufferBase(GL_SHADER_STORAGE_BUFFER,0,gMcNB);glBindBufferBase(GL_SHADER_STORAGE_BUFFER,1,gMcTB);
 glBindImageTexture(0,gMcTex[gMcCur^1],0,GL_FALSE,0,GL_WRITE_ONLY,GL_RGBA32F);
 glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,gMcTex[gMcCur]);glUniform1i(mcPrv,0);
 glBindImageTexture(1,gMcAov[gMcCur^1],0,GL_FALSE,0,GL_WRITE_ONLY,GL_RGBA16F);glActiveTexture(GL_TEXTURE1);glBindTexture(GL_TEXTURE_2D,gMcAov[gMcCur]);glUniform1i(mcAovPrev,1);glActiveTexture(GL_TEXTURE0);glUniform1i(mcN,gMcSamples+1);
 glUniform2i(mcSz,gMcW,gMcH);glUniform1i(mcOff,gMcRow);glUniform1i(mcFirst,gMcSamples==0?1:0);glUniform1i(mcFr,gMcFrame);glUniform1i(mcBn,gMcFinal?6:2);
 glUniform3f(mcCam,e.x,e.y,e.z);glUniform3f(mcF,f.x,f.y,f.z);glUniform3f(mcR,r.x,r.y,r.z);glUniform3f(mcU,u.x,u.y,u.z);
 float th=tanf(FOV/2);glUniform2f(mcTH,th*(float)gMcW/gMcH,th);
 V sd=norm(V{.4f,.8f,.5f});glUniform3f(mcSD,sd.x,sd.y,sd.z);glUniform3f(mcSC,3.2f,3.0f,2.8f);glUniform1f(mcSCos,.9995f);
 glDispatchCompute((gMcW+7)/8,(rows+7)/8,1);
 glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT|GL_TEXTURE_FETCH_BARRIER_BIT|GL_SHADER_STORAGE_BARRIER_BIT);
 gMcRow+=rows;if(gMcRow>=gMcH){gMcCur^=1;gMcSamples++;gMcRow=0;gMcFrame++;gDnDirty=true;}
 glUseProgram(gProg);}
void mcDenoise(){if(!gMcDn||!gDnProg||!gMcTex[0])return;int iters=gMcFinal?4:3;glUseProgram(gDnProg);
 glActiveTexture(GL_TEXTURE1);glBindTexture(GL_TEXTURE_2D,gMcAov[gMcCur]);glUniform1i(dnAov,1);
 for(int k=0;k<iters;k++){GLuint src=k==0?gMcTex[gMcCur]:gMcDnT[(k-1)&1];
  glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,src);glUniform1i(dnSrc,0);
  glBindImageTexture(0,gMcDnT[k&1],0,GL_FALSE,0,GL_WRITE_ONLY,GL_RGBA16F);
  glUniform2i(dnSz,gMcW,gMcH);glUniform1i(dnStep,1<<k);glUniform1i(dnI0,k==0?1:0);glUniform1f(dnPhi,.15f+2.f/sqrtf((float)std::max(gMcSamples,1)));
  glDispatchCompute((gMcW+7)/8,(gMcH+7)/8,1);glMemoryBarrier(GL_TEXTURE_FETCH_BARRIER_BIT|GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);}
 gMcDnRes=(iters-1)&1;gMcDnOK=true;glActiveTexture(GL_TEXTURE0);glUseProgram(gProg);}
void mcDraw(){glDisable(GL_DEPTH_TEST);glDisable(GL_BLEND);glUseProgram(gMcTm);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,(gMcDn&&gMcDnOK)?gMcDnT[gMcDnRes]:gMcTex[gMcCur]);
 glUniform1i(tmAcc,0);glUniform2i(tmSz,gMcW,gMcH);glBindVertexArray(meshes[3].vao);glDrawArrays(GL_TRIANGLES,0,6);glEnable(GL_BLEND);glUseProgram(gProg);}
void mcFrame(){mcStep();if(gDnDirty){if(gMcDn&&mcShow())mcDenoise();gDnDirty=false;}if(!mcShow())return;glViewport(0,0,W,H);mcDraw();}
static void mcWrite(void*c,void*d,int n){fwrite(d,1,n,(FILE*)c);}
void mcSave(){if(!mcShow()){toast("Nada para salvar");return;}
 glBindFramebuffer(GL_FRAMEBUFFER,gMcOutF);glViewport(0,0,gMcW,gMcH);mcDraw();
 std::vector<unsigned char> px((size_t)gMcW*gMcH*4);glReadPixels(0,0,gMcW,gMcH,GL_RGBA,GL_UNSIGNED_BYTE,px.data());
 glBindFramebuffer(GL_FRAMEBUFFER,0);glViewport(0,0,W,H);
 for(int y=0;y<gMcH/2;y++)for(int x=0;x<gMcW*4;x++)std::swap(px[(size_t)y*gMcW*4+x],px[(size_t)(gMcH-1-y)*gMcW*4+x]);
 std::string path;bool fb;FILE*f=openOut("png",path,fb);if(!f){toast("Erro ao salvar");return;}
 stbi_write_png_to_func(mcWrite,f,gMcW,gMcH,4,px.data(),gMcW*4);fclose(f);saved(path,fb);}
// ---------- projeto: novo / salvar / abrir / importar .mad ----------
struct Rd{const unsigned char*p;size_t n,i=0;bool ok=true;
 uint32_t u(){if(i+4>n){ok=false;return 0;}uint32_t v;memcpy(&v,p+i,4);i+=4;return v;}
 float f(){uint32_t v=u();float x;memcpy(&x,&v,4);return x;}int s(){return (int)u();}
 void b(void*d,size_t k){if(i+k>n){ok=false;memset(d,0,k);return;}memcpy(d,p+i,k);i+=k;}};
void clearScene(){for(size_t i=6;i<meshes.size();i++){glDeleteBuffers(1,&meshes[i].vbo);if(meshes[i].svbo)glDeleteBuffers(1,&meshes[i].svbo);glDeleteVertexArrays(1,&meshes[i].vao);}
 meshes.resize(6);objs.clear();skins.clear();sel=-1;tm=0;playing=false;parentMode=false;gImportOpen=false;gSigS=-1;mcReset();}
bool loadMAD(const std::string&path,bool replace){
 FILE*f=fopen(path.c_str(),"rb");if(!f){toast("Nao consegui abrir o arquivo");return false;}
 fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);if(sz<16){fclose(f);toast("Arquivo invalido");return false;}
 std::vector<unsigned char> buf(sz);size_t got=fread(buf.data(),1,sz,f);fclose(f);if((long)got!=sz){toast("Falha ao ler");return false;}
 Rd r{buf.data(),(size_t)sz};char mg[4];r.b(mg,4);uint32_t ver=r.u();
 if(memcmp(mg,"MAD2",4)!=0||ver!=2){toast("Formato .mad antigo ou invalido (so MAD2)");return false;}
 r.f();r.f();
 struct TM{std::vector<float> cpu,skin;float rad=1;};std::vector<TM> tms;uint32_t nm=r.u();if(nm>4096)r.ok=false;
 for(uint32_t i=0;i<nm&&r.ok;i++){TM t;uint32_t nc=r.u();if((size_t)nc*4>r.n-r.i){r.ok=false;break;}t.cpu.resize(nc);r.b(t.cpu.data(),(size_t)nc*4);t.rad=r.f();
  uint32_t ns=r.u();if((size_t)ns*4>r.n-r.i){r.ok=false;break;}t.skin.resize(ns);r.b(t.skin.data(),(size_t)ns*4);tms.push_back(std::move(t));}
 std::vector<Skin> sks;uint32_t nsk=r.u();if(nsk>4096)r.ok=false;
 for(uint32_t i=0;i<nsk&&r.ok;i++){Skin sk;uint32_t nj=r.u();if(nj>4096||(size_t)nj*136>r.n-r.i){r.ok=false;break;}
  for(uint32_t k=0;k<nj;k++){sk.j.push_back(r.s());M a,b;r.b(a.m,64);r.b(b.m,64);sk.ibm.push_back(a);sk.fz.push_back(b);}sks.push_back(sk);}
 std::vector<Obj> os;uint32_t no=r.u();if(no>100000)r.ok=false;
 for(uint32_t i=0;i<no&&r.ok;i++){Obj o;o.mesh=r.s();o.parent=r.s();o.skin=r.s();r.b(o.nm,24);o.nm[23]=0;o.len=r.f();o.met=r.f();o.rou=r.f();o.col.x=r.f();o.col.y=r.f();o.col.z=r.f();
  float c[9];r.b(c,36);memcpy(&o.cur.p.x,c,36);uint32_t nk=r.u();if(nk>100000||(size_t)nk*40>r.n-r.i){r.ok=false;break;}
  for(uint32_t k=0;k<nk;k++){Key kk;kk.t=r.f();float q[9];r.b(q,36);memcpy(&kk.x.p.x,q,36);o.k.push_back(kk);}os.push_back(o);}
 float cam[7];r.b(cam,28);
 if(!r.ok){toast("Arquivo .mad corrompido");return false;}
 if(replace)clearScene();
 int mb=(int)meshes.size(),sb2=(int)skins.size(),ob=(int)objs.size();
 for(auto&t:tms){Mesh mm=upload(t.cpu,GL_TRIANGLES);mm.rad=t.rad;if(!t.skin.empty())attachSkin(mm,t.skin);meshes.push_back(mm);}
 for(auto&sk:sks){for(auto&jj:sk.j)if(jj>=0)jj+=ob;skins.push_back(sk);}
 for(auto&o:os){if(o.mesh>=6)o.mesh=mb+(o.mesh-6);if(o.mesh<0||o.mesh>=(int)meshes.size())o.mesh=0;if(o.parent>=0)o.parent+=ob;
  if(o.skin>=0){o.skin+=sb2;if(o.skin>=(int)skins.size())o.skin=-1;}objs.push_back(o);}
 if(replace){yaw=cam[0];pitch=cam[1];cd=cam[2];tgt=V{cam[3],cam[4],cam[5]};tm=cam[6];}
 sel=os.empty()?-1:ob;toast(fm("Carregado: %d objetos",(int)os.size()));return true;}
double gNewT=-10;
void newProject(){double n=nowSec();if(n-gNewT>3){gNewT=n;toast("Toque em Novo de novo para limpar o projeto");return;}
 gNewT=-10;clearScene();gProj=fm("projeto_%ld",(long)(time(nullptr)%100000));toast("Novo projeto");}
void pickPath(const std::string&p){
 if(gPick==0){importPath(p);return;}
 if(gPick==1){if(loadMAD(p,true)){size_t sl=p.rfind('/');std::string n=sl==std::string::npos?p:p.substr(sl+1);size_t dt=n.rfind('.');if(dt!=std::string::npos)n=n.substr(0,dt);gProj=n;}}
 else loadMAD(p,false);}
bool setJoints(int si){if(si<0||si>=(int)skins.size())return false;Skin&sk=skins[si];int n=std::min((int)sk.j.size(),64);static M J[64];
 for(int k=0;k<n;k++){M jw=sk.j[k]>=0?worldM(sk.j[k]):(k<(int)sk.fz.size()?sk.fz[k]:id());J[k]=mul(jw,sk.ibm[k]);}
 glUniformMatrix4fv(uJL,n,GL_FALSE,J[0].m);return true;}
void drawBones(){for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];if(o.mesh!=5)continue;M mod=worldM(i);float wd=o.len*.35f;
  for(int k=0;k<4;k++){mod.m[k]*=wd;mod.m[4+k]*=o.len;mod.m[8+k]*=wd;}
  float h=(i==sel)?.55f:0;gMR[0]=0;gMR[1]=.5f;gSk=0;
  draw(meshes[5],mul(gVP,mod),mod,o.col.x+(.98f-o.col.x)*h,o.col.y+(.62f-o.col.y)*h,o.col.z+(.15f-o.col.z)*h,1,1);}}
// ---------- timeline estilo Maya/Houdini ----------
Rc gFldR[5]={};float gTrX0=0,gTrW=1,gBarY=0,gBarH=0,gDX0=0;int gDV0=0,gDV1=0;
void tri(float cx,float cy,float s,int dir){const float c=.93f;for(int i=0;i<10;i++){float h=2*s*(1-i/10.f);float x=dir>0?cx-s*.7f+i*s*.14f:cx+s*.7f-(i+1)*s*.14f;rect(x,cy-h/2,s*.15f,h,c,c,c);}}
void icon3(int id,float cx,float cy,float s,bool on){const float c=.93f;
 if(id==50){rect(cx-s*1.05f,cy-s*.8f,s*.3f,s*1.6f,c,c,c);tri(cx-s*.05f,cy,s*.7f,-1);tri(cx+s*.65f,cy,s*.7f,-1);}
 else if(id==54){rect(cx+s*.75f,cy-s*.8f,s*.3f,s*1.6f,c,c,c);tri(cx-s*.65f,cy,s*.7f,1);tri(cx+s*.05f,cy,s*.7f,1);}
 else if(id==51)tri(cx,cy,s,-1);else if(id==53)tri(cx,cy,s,1);
 else if(id==52)rect(cx-s*.75f,cy-s*.75f,s*1.5f,s*1.5f,c,c,c,1,s*.15f);
 else if(id==55){rect(cx-s*.9f,cy-s*.8f,s*.3f,s*1.6f,c,c,c);tri(cx+s*.2f,cy,s*.8f,-1);}
 else if(id==56){rect(cx+s*.6f,cy-s*.8f,s*.3f,s*1.6f,c,c,c);tri(cx-s*.2f,cy,s*.8f,1);}
 else if(id==57){for(int i=0;i<10;i++){float w=2*s*(1-i/10.f);rect(cx-w/2,cy-s*.5f+i*s*.1f,w,s*.11f,c,c,c);}}
 else if(id==7){rect(cx-s*.95f,cy-s*.55f,s*1.1f,s*1.1f,c,c,c,1,s*.55f);rect(cx-s*.6f,cy-s*.2f,s*.4f,s*.4f,.2f,.2f,.22f,1,s*.2f);
  rect(cx-s*.1f,cy-s*.12f,s*1.2f,s*.24f,c,c,c);rect(cx+s*.65f,cy,s*.22f,s*.55f,c,c,c);rect(cx+s*.35f,cy,s*.22f,s*.4f,c,c,c);}}
void jumpKey(int dir){if(sel<0||objs[sel].k.empty()){toast("Sem keyframes no objeto selecionado");return;}
 float best=0;bool f=false;for(auto&k:objs[sel].k){if(dir>0&&k.t>tm+.001f&&(!f||k.t<best)){best=k.t;f=true;}if(dir<0&&k.t<tm-.001f&&(!f||k.t>best)){best=k.t;f=true;}}
 if(!f){toast(dir>0?"Nao ha proximo keyframe":"Nao ha keyframe anterior");return;}tm=best;applyAnim();}
void delKey(){if(sel<0)return;auto&k=objs[sel].k;for(size_t i=0;i<k.size();i++)if(fabsf(k[i].t-tm)<.02f){k.erase(k.begin()+i);toast("Keyframe removido");return;}toast("Sem keyframe neste frame");}
bool tlHit(float x,float y,int&mode){
 for(int k=0;k<5;k++)if(inR(gFldR[k],x,y)){mode=k==4?27:23+k;gDX0=x;gDV0=k==0?gFS:k==1?gVS:k==2?gVE:k==3?gFE:(int)roundf(tm*24);return true;}
 float u=U();
 if(y>=gBarY-.6f*u&&y<=gBarY+gBarH+.6f*u&&x>=gTrX0-2*u&&x<=gTrX0+gTrW+2*u){
  float rng=(float)std::max(gFE-gFS,1);float b0=gTrX0+(gVS-gFS)/rng*gTrW,b1=gTrX0+(gVE-gFS)/rng*gTrW;gDX0=x;gDV0=gVS;gDV1=gVE;
  if(fabsf(x-b0)<2.2f*u)mode=20;else if(fabsf(x-b1)<2.2f*u)mode=21;
  else{if(x<b0||x>b1){int c=(int)roundf(gFS+(x-gTrX0)/gTrW*rng),w=gVE-gVS;int ns=std::clamp(c-w/2,gFS,std::max(gFE-w,gFS));gVS=ns;gVE=ns+w;gDV0=gVS;gDV1=gVE;}mode=22;}
  return true;}
 return false;}
void tlDrag(int mode,float x){float rng=(float)std::max(gFE-gFS,1);float u=U();int df=(int)roundf((x-gDX0)/(.55f*u));
 if(mode==20)gVS=std::clamp((int)roundf(gFS+(x-gTrX0)/gTrW*rng),gFS,gVE-5);
 else if(mode==21)gVE=std::clamp((int)roundf(gFS+(x-gTrX0)/gTrW*rng),gVS+5,gFE);
 else if(mode==22){int w=gDV1-gDV0;int sh=(int)roundf((x-gDX0)/gTrW*rng);int ns=std::clamp(gDV0+sh,gFS,std::max(gFE-w,gFS));gVS=ns;gVE=ns+w;}
 else if(mode==23){gFS=std::clamp(gDV0+df,0,gFE-10);syncRange();}
 else if(mode==24)gVS=std::clamp(gDV0+df,gFS,gVE-5);
 else if(mode==25)gVE=std::clamp(gDV0+df,gVS+5,gFE);
 else if(mode==26){gFE=std::clamp(gDV0+df,gFS+10,2400);syncRange();}
 else if(mode==27){int f=std::clamp(gDV0+df,gFS,gFE);tm=f/24.f;applyAnim();}
 if(mode>=23&&mode<=26){float a=gFS/24.f,b=gFE/24.f;if(tm<a)tm=a;if(tm>b)tm=b;applyAnim();}}
void frameTap(float x){float rel=(x-gFldR[4].x)/std::max(gFldR[4].w,1.f);int f=(int)roundf(tm*24);if(rel<.33f)f--;else if(rel>.66f)f++;tm=std::clamp(f,gFS,gFE)/24.f;applyAnim();}
void frame(){
 bool post=gSSAO&&gPostOK;glBindFramebuffer(GL_FRAMEBUFFER,post?(gMsOK?gMsFbo:gFbo):0);
 glViewport(0,0,W,H);glClearColor(.24f,.24f,.26f,1);glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
 glEnable(GL_DEPTH_TEST);
 gVP=mul(persp(FOV,(float)W/H,.1f,100),lookAt(camEye(),tgt,{0,1,0}));{V e_=camEye();glUniform3f(uCamL,e_.x,e_.y,e_.z);}
 draw(meshes[4],gVP,id(),.34f,.34f,.37f,1,0);
 auto ln=[&](V c,V sc,float r,float g,float b){T t;t.p=c;t.s=sc;M m=model(t);draw(meshes[0],mul(gVP,m),m,r,g,b,1,0);};
 ln({0,0,0},{20,.014f,.014f},.85f,.28f,.3f);ln({0,0,0},{.014f,.014f,20},.3f,.5f,.9f);
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];if(o.mesh==5)continue;M mod=worldM(i);bool skd=o.skin>=0&&meshes[o.mesh].skinned&&setJoints(o.skin);if(skd)mod=id();gSk=skd?1.f:0.f;float h=(i==sel)?.35f:0;gMR[0]=o.met;gMR[1]=o.rou;
  draw(meshes[o.mesh],mul(gVP,mod),mod,o.col.x+(1-o.col.x)*h,o.col.y+(1-o.col.y)*h,o.col.z+(1-o.col.z)*h,1,1);}
 gMR[0]=0;gMR[1]=.5f;gSk=0;if(post)runPost();mcFrame();
 glDisable(GL_DEPTH_TEST);
 if(gBones)drawBones();
 if(sel>=0&&tool<3)drawGizmo();
 gBtn.clear();gBlock.clear();float u=U(),ML_=ML(),hH=7.2f*u;
 // cabecalho: icones pequenos a esquerda
 rect(0,0,W,hH,.15f,.15f,.16f,.96f);gBlock.push_back({0,0,(float)W,hH});
 {static const int RW[12]={0,1,2,10,3,4,5,6,11,12,8,9};static const int GP[12]={0,0,0,0,1,0,0,0,1,0,1,0};
  float bs=5.8f*u,gp=.45f*u,x=ML_,by=(hH-bs)/2;
  for(int k=0;k<12;k++){int id=RW[k];if(GP[k])x+=1.1f*u;
   bool on=(id>=3&&id<=6&&tool==id-3)||(id==8&&playing)||(id==11&&parentMode)||gFlash[id]>0;
   rect(x,by,bs,bs,on?.28f:.33f,on?.45f:.33f,on?.7f:.35f,1,.9f*u);icon2(id,x+bs/2,by+bs/2,bs*.27f,on);gBtn.push_back({{x,by,bs,bs},id});x+=bs+gp;}
  float tp=.4f*u;char hb[64];snprintf(hb,64,"%.16s  v16  %d FPS",gProj.c_str(),(int)(gFps+.5f));text(hb,x+1.5f*u,hH/2-2.5f*tp,tp,.6f,.6f,.66f);}
 {float bs=5.8f*u,gp=.45f*u,by=(hH-bs)/2,xr=W-ML_;
  static const int PJ[3]={42,41,40};
  for(int k=0;k<3;k++){int id=PJ[k];bool on=gFlash[id]>0||(id==41&&gImportOpen&&gPick==1);float x=xr-bs;
   rect(x,by,bs,bs,on?.28f:.33f,on?.45f:.33f,on?.7f:.35f,1,.9f*u);icon2(id,x+bs/2,by+bs/2,bs*.27f,on);gBtn.push_back({{x,by,bs,bs},id});xr=x-gp;}
  xr-=.8f*u;
  const char*rl[4]={"Import glTF","Import MAD","Export glTF","Export MAD"};const int rid[4]={15,43,14,13};float ph=5*u,py=(hH-ph)/2,ps=ph*.072f;
  for(int i=3;i>=0;i--){float w=tw(rl[i],ps)+4*u,x=xr-w;bool on=gFlash[rid[i]]>0||(rid[i]==15&&gImportOpen&&gPick==0)||(rid[i]==43&&gImportOpen&&gPick==2);
   pill(x,py,w,ph,rid[i],rl[i],on,i<2?.2f:.33f,i<2?.38f:.33f,i<2?.55f:.35f);xr=x-.8f*u;}}
 { // painel de render (esquerda)
  float px=ML_,py=hH+1.5f*u,pw2=27*u,rh=4.4f*u,tp2=.38f*u;panel(px,py,pw2,rh*5+2.4f*u,1*u);
  auto sld=[&](int i,float yy,const char*lab,float v){float lw=9.5f*u,sx=px+lw,sw=pw2-lw-1.4f*u;text(lab,px+1.2f*u,yy+rh/2-2.5f*tp2,tp2,.85f,.85f,.88f);
   rect(sx,yy+rh/2-.45f*u,sw,.9f*u,.1f,.1f,.11f,1,.45f*u);rect(sx,yy+rh/2-.45f*u,sw*v,.9f*u,.28f,.45f,.7f,1,.45f*u);
   rect(sx+sw*v-.7f*u,yy+rh/2-1.1f*u,1.4f*u,2.2f*u,.95f,.95f,.95f,1,.7f*u);gBtn.push_back({{sx-.8f*u,yy,sw+1.6f*u,rh},300+i});gSlX[i]=sx;gSlW[i]=sw;};
  float y1=py+1.2f*u;
  sld(0,y1,"Metal",sel>=0?objs[sel].met:0.f);sld(1,y1+rh,"Rough",sel>=0?objs[sel].rou:.5f);sld(2,y1+2*rh,"AO",gAOs);
  pill(px+1.2f*u,y1+3*rh+.3f*u,pw2-2.4f*u,rh-.6f*u,16,(gSSAO&&gPostOK)?"SSAO: on":"SSAO: off",gSSAO,.3f,.3f,.33f);
  pill(px+1.2f*u,y1+4*rh+.3f*u,pw2-2.4f*u,rh-.6f*u,17,gBones?"Bones: on":"Bones: off",gBones,.3f,.3f,.33f);
  gBtn.push_back({{px,py,pw2,rh*5+2.4f*u},299});}
 { // painel Monte Carlo / path tracing
  float px=ML_,py=hH+1.5f*u+(5*4.4f+2.4f)*u+1.5f*u,pw2=27*u,rh=4.4f*u,tp2=.38f*u,y1=py+1.0f*u,bw_=pw2-2.4f*u,bh_=rh-.6f*u;
  panel(px,py,pw2,rh*7+1.6f*u,1*u);
  if(!gMcOK){text("MC indisponivel (precisa de ES 3.1)",px+1.2f*u,y1+rh/2-2.5f*tp2,tp2*.85f,.85f,.55f,.5f);}
  else{bool done=gMcFinal&&gMcSamples>=gMcSpp;
   pill(px+1.2f*u,y1,bw_,bh_,30,gMcPrev?"Preview MC: on":"Preview MC: off",gMcPrev,.3f,.3f,.33f);
   pill(px+1.2f*u,y1+rh,bw_,bh_,31,gMcFinal?(done?"Fechar render":"Parar render"):"Render final",gMcFinal,.5f,.34f,.12f);
   pill(px+1.2f*u,y1+2*rh,bw_,bh_,33,fm("Amostras: %d",gMcSpp).c_str(),false,.3f,.3f,.33f);
   pill(px+1.2f*u,y1+3*rh,bw_,bh_,34,gMcGround?"Chao: on":"Chao: off",gMcGround,.3f,.3f,.33f);
   pill(px+1.2f*u,y1+4*rh,bw_,bh_,35,gMcDn?"Denoise: on":"Denoise: off",gMcDn,.3f,.3f,.33f);
   pill(px+1.2f*u,y1+5*rh,bw_,bh_,32,"Salvar PNG",false,.2f,.38f,.55f);
   char sb[64];snprintf(sb,64,"%d / %d spp  %dx%d",gMcSamples,gMcFinal?gMcSpp:128,gMcW,gMcH);text(sb,px+1.2f*u,y1+6*rh+rh/2-2.5f*tp2,tp2*.9f,.7f,.7f,.75f);}
  gBtn.push_back({{px,py,pw2,rh*7+1.6f*u},299});}
 // outliner + transform (direita)
 float pw=30*u,rx=W-ML_-pw,ry=navY()+navR()+1.5f*u,rh=4.4f*u,tpx=.38f*u;
 int n=(int)objs.size(),rows=std::min(n,3),st=(n>3&&sel>=0)?std::clamp(sel-2,0,n-3):0;
 float oh=4*u+std::max(rows,1)*rh+1*u;panel(rx,ry,pw,oh,1*u);
 text("Scene",rx+1.5f*u,ry+2*u-2.5f*tpx,tpx,.6f,.6f,.65f);
 if(!n)text("Empty - tap + Cube",rx+1.5f*u,ry+4*u+2.2f*u-2.5f*tpx,tpx,.5f,.5f,.55f);
 for(int r=0;r<rows;r++){int i=st+r;float yy=ry+4*u+r*rh;
  if(i==sel)rect(rx+.6f*u,yy,pw-1.2f*u,rh-.2f*u,.28f,.45f,.7f,1,.7f*u);
  rect(rx+1.6f*u,yy+1.3f*u,1.8f*u,1.8f*u,objs[i].col.x,objs[i].col.y,objs[i].col.z,1,.9f*u);
  text(objs[i].nm,rx+4.6f*u,yy+2.2f*u-2.5f*tpx,tpx,.93f,.93f,.93f);gBtn.push_back({{rx,yy,pw,rh},100+i});}
 if(sel>=0){T&t=objs[sel].cur;float ty=ry+oh+1.5f*u;panel(rx,ty,pw,4*u+3*rh+1*u,1*u);
  
  float lw=5.5f*u,fw=(pw-lw-1.2f*u)/3;static const char*XYZ[3]={"X","Y","Z"};
  for(int j=0;j<3;j++)tcen(XYZ[j],rx+lw+j*fw+fw/2,ty+2*u,tpx,AC[j][0],AC[j][1],AC[j][2]);
  static const char*LB3[3]={"Loc","Rot","Scl"};V val[3]={t.p,t.r*(180/PI),t.s};
  for(int k=0;k<3;k++){float yy=ty+4*u+k*rh;text(LB3[k],rx+1.2f*u,yy+2.2f*u-2.5f*tpx,tpx,.75f,.75f,.78f);
   for(int j=0;j<3;j++){char b[16];snprintf(b,16,k==1?"%.1f":"%.2f",(&val[k].x)[j]);float fx=rx+lw+j*fw;
    rect(fx,yy+.3f*u,fw-.5f*u,rh-.6f*u,.25f,.25f,.27f,1,.6f*u);tcen(b,fx+(fw-.5f*u)/2,yy+2.2f*u,tpx*.95f,.92f,.92f,.92f);}}}
 // timeline estilo Maya/Houdini (compacta)
 float TH=17.5f*u,tT=100*u-3.6f*u-TH,tw_=W-2*ML_;panel(ML_,tT,tw_,TH,1*u);
 {float x0=ML_+.9f*u,wd=tw_-1.8f*u;
  { // linha 1: transporte, frame atual, keys
   float y=tT+.8f*u,h=5.4f*u,bwt=5.6f*u,gp=.3f*u,x=x0;static const int TID[5]={50,51,52,53,54};
   for(int k=0;k<5;k++){bool on=(k==2&&!playing)||(k==1&&playing&&gPlayDir<0)||(k==3&&playing&&gPlayDir>0)||gFlash[TID[k]]>0;
    rect(x,y,bwt,h,on?.28f:.27f,on?.45f:.27f,on?.7f:.29f,1,.7f*u);icon3(TID[k],x+bwt/2,y+h/2,h*.26f,on);gBtn.push_back({{x,y,bwt,h},TID[k]});x+=bwt+gp;}
   x+=1.0f*u;float fw=11*u;rect(x,y,fw,h,.09f,.09f,.1f,1,.7f*u);gFldR[4]={x,y,fw,h};
   char fb_[16];snprintf(fb_,16,"%d",(int)roundf(tm*24));tcen(fb_,x+fw/2,y+h/2,.46f*u,.95f,.95f,.95f);
   tcen("<",x+1.3f*u,y+h/2,.36f*u,.5f,.5f,.55f);tcen(">",x+fw-1.3f*u,y+h/2,.36f*u,.5f,.5f,.55f);x+=fw+gp+.6f*u;
   for(int k=0;k<2;k++){int id=55+k;float bw2=4.4f*u;rect(x,y,bw2,h,.27f,.27f,.29f,1,.7f*u);icon3(id,x+bw2/2,y+h/2,h*.2f,false);gBtn.push_back({{x,y,bw2,h},id});x+=bw2+gp;}
   x+=1.2f*u;bool kon=gFlash[7]>0;rect(x,y,h,h,kon?.28f:.2f,kon?.45f:.2f,kon?.7f:.22f,1,h/2);icon3(7,x+h/2,y+h/2,h*.28f,false);gBtn.push_back({{x,y,h,h},7});x+=h+.3f*u;
   float dw=3.2f*u;rect(x,y,dw,h,.22f,.22f,.24f,1,.7f*u);icon3(57,x+dw/2,y+h/2,h*.14f,false);gBtn.push_back({{x,y,dw,h},57});}
  { // linha 2: regua
   float ry=tT+7.0f*u,rh=6.0f*u,ppf;gTX0=x0+.6f*u;gTW=wd-1.2f*u;gTrack={x0,ry,wd,rh};gBlock.push_back(gTrack);
   rect(x0,ry,wd,rh,.12f,.12f,.13f,1,.6f*u);ppf=gTW/(float)std::max(gVE-gVS,1);float yl=ry+4.3f*u;
   if(sel>=0)for(auto&k:objs[sel].k){float kx=tx(k.t);if(kx<gTX0-1||kx>gTX0+gTW+1)continue;float bw3=std::clamp(ppf*.85f,.5f*u,1.8f*u);rect(kx-bw3/2,yl-1.9f*u,bw3,3.8f*u,.3f,.62f,.08f);}
   rect(x0+.3f*u,yl-.05f*u,wd-.6f*u,.1f*u,.6f,.6f,.63f);
   static const int ST[8]={1,2,5,10,20,25,50,100};int step=100;for(int k=0;k<8;k++)if(ST[k]*ppf>=9*u){step=ST[k];break;}
   int minor=step>=10?step/5:(step>=5?1:0);
   for(int f=gVS;f<=gVE;f++){float xx=tx(f/24.f);bool major=f%step==0;
    if(major){rect(xx-.08f*u,yl-1.8f*u,.16f*u,3.6f*u,.78f,.78f,.8f);char b[12];snprintf(b,12,"%d",f);tcen(b,xx,ry+1.3f*u,.32f*u,.6f,.6f,.64f);}
    else if(minor>0&&f%minor==0)rect(xx-.06f*u,yl-.9f*u,.12f*u,1.8f*u,.5f,.5f,.54f);}
   float cf=tm*24;if(cf>=gVS-.01f&&cf<=gVE+.01f){float px=tx(tm);char b[12];snprintf(b,12,"%d",(int)roundf(cf));float bw3=tw(b,.4f*u)+3.2f*u;
    rect(px-.06f*u,ry+3.6f*u,.12f*u,rh-3.6f*u,1,1,1);rect(px-bw3/2-.15f*u,ry+.1f*u,bw3+.3f*u,3.5f*u,.95f,.95f,.95f,1,.6f*u);
    rect(px-bw3/2,ry+.25f*u,bw3,3.2f*u,.05f,.05f,.06f,1,.5f*u);tcen(b,px,ry+1.85f*u,.4f*u,1,1,1);dia(px,ry+3.6f*u,1.4f*u,.95f,.95f,.95f);}}
  { // linha 3: intervalo global e janela visivel
   float ry3=tT+13.6f*u,h3=3.4f*u,fw3=8.2f*u;
   gFldR[0]={x0,ry3,fw3,h3};gFldR[1]={x0+fw3+.6f*u,ry3,fw3,h3};gFldR[2]={x0+wd-2*fw3-.6f*u,ry3,fw3,h3};gFldR[3]={x0+wd-fw3,ry3,fw3,h3};
   int vals[4]={gFS,gVS,gVE,gFE};
   for(int k=0;k<4;k++){bool inn=k==1||k==2;rect(gFldR[k].x,ry3,fw3,h3,inn?.07f:.16f,inn?.07f:.16f,inn?.08f:.18f,1,.5f*u);
    char b[12];snprintf(b,12,"%d",vals[k]);tcen(b,gFldR[k].x+fw3/2,ry3+h3/2,.4f*u,.92f,.92f,.92f);}
   gTrX0=gFldR[1].x+fw3+1.2f*u;gTrW=gFldR[2].x-1.2f*u-gTrX0;gBarY=ry3;gBarH=h3;
   float rng=(float)std::max(gFE-gFS,1),b0=gTrX0+(gVS-gFS)/rng*gTrW,b1=gTrX0+(gVE-gFS)/rng*gTrW,cy=ry3+h3/2;
   rect(gTrX0,cy-.2f*u,gTrW,.4f*u,.07f,.07f,.08f,1,.2f*u);rect(b0,cy-.35f*u,std::max(b1-b0,.5f*u),.7f*u,.55f,.55f,.58f,1,.3f*u);
   rect(b0-.5f*u,ry3+.3f*u,1.0f*u,h3-.6f*u,.75f,.75f,.78f,1,.3f*u);rect(b1-.5f*u,ry3+.3f*u,1.0f*u,h3-.6f*u,.75f,.75f,.78f,1,.3f*u);}}
 if(gImportOpen){float pw2=82*u,rh2=4.8f*u,tp2=.42f*u;int n=std::max((int)gFiles.size(),1);float ph2=6.5f*u+n*rh2+1.5f*u,px2=(W-pw2)/2,py2=(H-ph2)/2;
  panel(px2,py2,pw2,ph2,1.2f*u);text((gPick==0?"Importar glTF / GLB / ZIP":gPick==1?"Abrir projeto (.mad)":"Importar .mad"),px2+2*u,py2+2.6f*u-2.5f*tp2,tp2,.7f,.7f,.75f);
  if(gFiles.empty()){text((gPick==0?"Nenhum .gltf/.glb/.zip em Download.":"Nenhum .mad em Download."),px2+2*u,py2+8.1f*u-2.5f*tp2,tp2,.9f,.9f,.9f);
   text("Ative Acesso a todos os arquivos nas permissoes do app.",px2+2*u,py2+8.1f*u+rh2-2.5f*tp2,tp2*.9f,.6f,.6f,.65f);}
  for(size_t i=0;i<gFiles.size();i++){float yy=py2+6.5f*u+i*rh2;rect(px2+1*u,yy,pw2-2*u,rh2-.4f*u,.24f,.24f,.27f,1,.7f*u);
   std::string nf=gFiles[i];size_t s1=nf.rfind('/');if(s1!=std::string::npos&&s1>0){size_t s2=nf.rfind('/',s1-1);nf=nf.substr(s2==std::string::npos?0:s2+1);}if(nf.size()>38)nf=nf.substr(nf.size()-38);
   text(nf.c_str(),px2+2.5f*u,yy+rh2/2-.2f*u-2.5f*tp2,tp2,.95f,.95f,.95f);gBtn.push_back({{px2+1*u,yy,pw2-2*u,rh2},200+(int)i});}
  gBtn.push_back({{px2,py2,pw2,ph2},299});}
 if(gToastT>0){float tt=.4f*u,w2=tw(gToast.c_str(),tt)+4*u,bx=(W-w2)/2,by=tT-7*u;rect(bx,by,w2,5.4f*u,.08f,.08f,.08f,.93f,1*u);text(gToast.c_str(),bx+2*u,by+2.7f*u-2.5f*tt,tt,1,1,1);}
 drawNav();
 eglSwapBuffers(dpy,surf);}

// ---------- input ----------
void press(int i){
 if(i>=0&&i<64)gFlash[i]=.35f;
 if(i>=200){int k=i-200;if(i!=299){gImportOpen=false;if(k<(int)gFiles.size())pickPath(gFiles[k]);}return;}
 if(i<3)addObj(i);else if(i<7)tool=i-3;
 else if(i==7)insertKey();else if(i==8){playing=!playing;if(playing)gPlayDir=1;}
 else if(i==9){if(sel>=0)delObj(sel);}
 else if(i==10)addObj(5);
 else if(i==11){if(sel<0)toast("Selecione um objeto");else{parentMode=true;toast("Toque no objeto PAI");}}
 else if(i==12){if(sel>=0)clearParent(sel);}
 else if(i==13||i==14){if(!filesGranted())needFiles();else if(i==13)exportMAD();else exportGLTF();}
 else if(i==15||i==41||i==43){if(!filesGranted())needFiles();else{gPick=i==15?0:i==41?1:2;scanFiles();gImportOpen=true;}}
 else if(i==40)newProject();
 else if(i==42){if(!filesGranted())needFiles();else saveProject();}
 else if(i==35){gMcDn=!gMcDn;gDnDirty=true;}
 else if(i==16)gSSAO=!gSSAO;
 else if(i==17)gBones=!gBones;
 else if(i==30){gMcPrev=!gMcPrev;if(gMcPrev)gMcFinal=false;gMcHaveCam=false;gSigS=-1;mcReset();}
 else if(i==31){gMcFinal=!gMcFinal;if(gMcFinal)gMcPrev=false;gMcHaveCam=false;gSigS=-1;mcReset();}
 else if(i==32){if(!filesGranted())needFiles();else mcSave();}
 else if(i==33)gMcSpp=gMcSpp>=1024?16:gMcSpp*4;
 else if(i==34){gMcGround=!gMcGround;gSigS=-1;}
 else if(i==50){tm=gFS/24.f;applyAnim();}else if(i==51){playing=true;gPlayDir=-1;}else if(i==52)playing=false;else if(i==53){playing=true;gPlayDir=1;}else if(i==54){tm=gFE/24.f;applyAnim();}
 else if(i==55)jumpKey(-1);else if(i==56)jumpKey(1);else if(i==57)delKey();
 else if(i>=20&&i<=23){if(i==20)tm=0;else if(i==21)tm=std::max(0.f,tm-1/24.f);else if(i==22)tm=std::min(DUR,tm+1/24.f);else tm=DUR;applyAnim();}}
void scrub(float x){int f=(int)roundf(gVS+std::clamp((x-gTX0)/gTW,0.f,1.f)*(gVE-gVS));tm=std::clamp(f,gFS,gFE)/24.f;applyAnim();}
void pick(float x,float y){
 if(gBones){int bb=-1;float bd=40;for(int i=0;i<(int)objs.size();i++){if(objs[i].mesh!=5)continue;M w=worldM(i);
   V hd{w.m[12],w.m[13],w.m[14]},tl=hd+V{w.m[4],w.m[5],w.m[6]}*objs[i].len;float hx,hy,qx,qy;if(!prj(hd,hx,hy)||!prj(tl,qx,qy))continue;
   float vx=qx-hx,vy=qy-hy,tt=std::clamp(((x-hx)*vx+(y-hy)*vy)/(vx*vx+vy*vy+1e-3f),0.f,1.f);float dd=hypotf(x-hx-vx*tt,y-hy-vy*tt);if(dd<bd){bd=dd;bb=i;}}
  if(bb>=0){if(parentMode)finishParent(bb);else sel=bb;return;}}
 V e=camEye(),f=norm(tgt-e),s2=norm(cross(f,V{0,1,0})),u=cross(s2,f);
 float th=tanf(FOV/2),as=(float)W/H;V d=norm(f+s2*((2*x/W-1)*th*as)+u*((1-2*y/H)*th));
 static const float RF[3]={.87f,.5f,1.42f};int best=-1;float bt=1e9f;
 for(int i=0;i<(int)objs.size();i++){Obj&o=objs[i];V c=wp(i);float r;
  if(o.mesh==5){M w=worldM(i);c=c+V{w.m[4],w.m[5],w.m[6]}*(o.len*.5f);r=o.len*.35f;}
  else r=(o.mesh<3?RF[o.mesh]:meshes[o.mesh].rad)*std::max({o.cur.s.x,o.cur.s.y,o.cur.s.z});
  V oc=e-c;float b=dot(oc,d),cc=dot(oc,oc)-r*r,ds=b*b-cc;if(ds<0)continue;
  float tt=-b-sqrtf(ds);if(tt>0&&tt<bt){bt=tt;best=i;}}
 if(parentMode)finishParent(best);else sel=best;}
void orbit(float dx,float dy){yaw-=dx*.006f;pitch=std::clamp(pitch+dy*.006f,-1.5f,1.5f);}
void gdrag(float dx,float dy){
 Obj&ob=objs[sel];T&t=ob.cur;V o=wp(sel);float ox,oy,ex,ey;
 if(tool==1){float px,py,qx,qy;if(!prj(ringPt(gAxis,gIdx+1),px,py)||!prj(ringPt(gAxis,gIdx+31),qx,qy))return;
  float vx=px-qx,vy=py-qy,l=hypotf(vx,vy);if(l<1)return;rotateWorld(ob,gAxis,(dx*vx+dy*vy)/l*.012f);return;}
 if(!prj(o,ox,oy)||!prj(o+AX[gAxis]*gl(),ex,ey))return;
 float vx=ex-ox,vy=ey-oy,k=(dx*vx+dy*vy)/(vx*vx+vy*vy+1e-3f);
 if(tool==0){V nw=o+AX[gAxis]*(k*gl());t.p=ob.parent>=0?invPt(worldM(ob.parent),nw):nw;}
 else if(ob.mesh==5)ob.len=std::max(.05f,ob.len*(1+k));
 else{float&sc=(&t.s.x)[gAxis];sc=std::max(.05f,sc*(1+k));}}
void snap(float x,float y){ND d[6];navPts(d);
 for(auto&e:d)if(hypotf(x-e.x,y-e.y)<H*.035f){
  if(e.a==0){yaw=e.pos?PI/2:-PI/2;pitch=0;}else if(e.a==1)pitch=e.pos?1.45f:-1.45f;else{yaw=e.pos?0.f:PI;pitch=0;}return;}}
int32_t onInput(android_app*,AInputEvent*e){
 static int mode=0;static float lx,ly,sx,sy,pinch;static bool moved,rl;
 if(AInputEvent_getType(e)!=AINPUT_EVENT_TYPE_MOTION)return 0;
 int act=AMotionEvent_getAction(e)&AMOTION_EVENT_ACTION_MASK,n=(int)AMotionEvent_getPointerCount(e);
 float x=AMotionEvent_getX(e,0),y=AMotionEvent_getY(e,0);
 if(act==AMOTION_EVENT_ACTION_DOWN){
  moved=false;rl=true;sx=x;sy=y;pinch=0;gDrag=false;mode=-1;
  for(auto&b:gBtn)if(inR(b.r,x,y)){if(b.id>=300&&b.id<=302){setSlider(b.id-300,x);mode=6+b.id-300;break;}if(b.id>=200||b.id<100)press(b.id);else{if(parentMode)finishParent(b.id-100);else sel=b.id-100;}mode=2;break;}
  if(mode<0&&gImportOpen){gImportOpen=false;mode=2;}
  if(mode<0){
   if(tlHit(x,y,mode)){}
   else if(inR(gTrack,x,y)){mode=3;scrub(x);}
   else if(hypotf(x-navX(),y-navY())<navR()+12)mode=4;
   else{bool blk=false;for(auto&r:gBlock)if(inR(r,x,y))blk=true;
    if(blk)mode=2;else{int a=hitGizmo(x,y);if(a>=0){gAxis=a;gDrag=true;mode=5;}else mode=1;}}}
 }else if(act==AMOTION_EVENT_ACTION_POINTER_DOWN){moved=true;rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_POINTER_UP){rl=true;pinch=0;}
 else if(act==AMOTION_EVENT_ACTION_MOVE){
  if(mode==3)scrub(x);
  else if(mode>=20){if(hypotf(x-sx,y-sy)>20)moved=true;tlDrag(mode,x);}
  else if(mode>=6)setSlider(mode-6,x);
  else if(mode==1&&n>=2){float d=hypotf(AMotionEvent_getX(e,1)-x,AMotionEvent_getY(e,1)-y);
   if(pinch>0&&d>1)cd=std::clamp(cd*pinch/d,2.f,40.f);pinch=d;moved=true;}
  else if(mode==1||mode==4||mode==5){
   if(rl){rl=false;lx=x;ly=y;}
   else{float dx=x-lx,dy=y-ly;lx=x;ly=y;if(hypotf(x-sx,y-sy)>20)moved=true;
    if(mode==5)gdrag(dx,dy);else if(moved)orbit(dx,dy);}}
 }else if(act==AMOTION_EVENT_ACTION_UP||act==AMOTION_EVENT_ACTION_CANCEL){
  if(mode==1&&!moved)pick(x,y);if(mode==4&&!moved)snap(x,y);if(mode==27&&!moved)frameTap(x);mode=0;gDrag=false;}
 return 1;}
void onCmd(android_app*a,int32_t c){
 if(c==APP_CMD_INIT_WINDOW&&a->window){if(initEGL(a->window)){initGL();ready=true;}}
 else if(c==APP_CMD_TERM_WINDOW){ready=false;termEGL();}}

void android_main(android_app*app){
 app->onAppCmd=onCmd;app->onInputEvent=onInput;
 gProj=fm("projeto_%ld",(long)(time(nullptr)%100000));gApp=app;if(app->activity)gDir=app->activity->externalDataPath?app->activity->externalDataPath:app->activity->internalDataPath;
 auto now=[](){timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;};
 double last=now();
 while(true){
  int ev;android_poll_source*src;
  while(ALooper_pollOnce(ready?0:-1,nullptr,&ev,(void**)&src)>=0){
   if(src)src->process(app,src);
   if(app->destroyRequested){termEGL();return;}}
  if(ready){double t=now();float dt=(float)(t-last);last=t;gDt=dt;gToastT-=dt;gFAcc+=dt;gFN++;if(gFAcc>=.5f){gFps=gFN/gFAcc;gFAcc=0;gFN=0;}for(float&fl:gFlash)if(fl>0)fl-=dt;
   if(playing){tm+=dt*gPlayDir;float a_=gFS/24.f,b_=gFE/24.f;if(tm>b_)tm=a_;if(tm<a_)tm=b_;applyAnim();}
   frame();}else last=now();}}
