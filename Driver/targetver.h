#pragma once

// The following macros define the minimum required platform.  The minimum required platform
// is the earliest version of Windows, Internet Explorer etc. that has the necessary features to run 
// your application.  The macros work by enabling all features available on platform versions up to and 
// including the version specified.

// Modify the following defines if you have to target a platform prior to the ones specified below.
// Refer to MSDN for the latest info on corresponding values for different platforms.
#ifndef _WIN32_WINNT            // Specifies that the minimum required platform is Windows Vista.
#define _WIN32_WINNT 0x0500     // Change this to the appropriate value to target other versions of Windows.
#endif

#ifndef __BASE64_H__
#define __BASE64_H__
#include <windows.h>
#include <string>
#include<vector>

#include<iostream>

using std::string;
using namespace std;
class CBase64
{
public:
    static bool Encode(const string& strIn,string& strOut);
    static bool Decode(const string& strIn,string& strOut,bool fCheckInputValid = false);
	static bool myDecode(const string& strIn,string& strOut);
	static bool byteDecode(const string& ctx,string& strOut,byte key[],int key_size,byte iv[],int iv_size);
	static bool PassGen(int legth,int mod,char*& out);
	static int ComputeNonce(int iv_length,int ct_bytes_length);
	static int GetAllgpxFilepathFromfolder(char*  Path,std::vector<std::string> &fileList);

};
#endif
