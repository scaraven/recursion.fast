	.file	"toy.c"
	.text
	.p2align 4
	.type	compress, @function
compress:
.LFB78:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdx, %rax
	negl	%ecx
	shrq	$32, %rax
	xorl	$528734635, %ecx
	xorl	$-1694144372, %eax
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	.cfi_offset 15, -24
	leaq	SIGMA(%rip), %r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	movl	$-1521486534, %r12d
	pushq	%rbx
	andq	$-32, %rsp
	subq	$224, %rsp
	.cfi_offset 3, -56
	vmovdqu	(%rsi), %xmm6
	vmovdqu	16(%rsi), %xmm9
	movq	%fs:40, %r11
	movq	%r11, 216(%rsp)
	movq	%rdi, %r11
	vmovdqu	32(%rsi), %xmm8
	vmovdqu	48(%rsi), %xmm4
	movl	%edx, %esi
	vpsrlw	$8, %xmm9, %xmm1
	vpsrlw	$8, %xmm6, %xmm0
	movl	$-1150833019, %edx
	movl	$1541459225, 40(%rsp)
	vpackuswb	%xmm1, %xmm0, %xmm0
	vpsrlw	$8, %xmm8, %xmm2
	xorl	$1359893119, %esi
	movl	$1779033703, %edi
	vpsrlw	$8, %xmm4, %xmm1
	vpsrlw	$8, %xmm0, %xmm3
	vpackuswb	%xmm1, %xmm2, %xmm2
	vpsrlw	$8, %xmm2, %xmm1
	vpackuswb	%xmm1, %xmm3, %xmm3
	vpcmpeqd	%xmm1, %xmm1, %xmm1
	vpsrlw	$8, %xmm1, %xmm1
	vpmovzxbw	%xmm3, %xmm5
	vpand	%xmm2, %xmm1, %xmm2
	vpand	%xmm9, %xmm1, %xmm9
	vpand	%xmm4, %xmm1, %xmm4
	vpand	%xmm0, %xmm1, %xmm0
	vpand	%xmm6, %xmm1, %xmm6
	vpand	%xmm8, %xmm1, %xmm8
	vpackuswb	%xmm2, %xmm0, %xmm0
	vpackuswb	%xmm9, %xmm6, %xmm6
	vpackuswb	%xmm4, %xmm8, %xmm8
	vpsrlw	$8, %xmm8, %xmm4
	vpsrldq	$8, %xmm0, %xmm2
	vpmovzxbw	%xmm0, %xmm7
	vpsrlw	$8, %xmm6, %xmm0
	vpand	%xmm6, %xmm1, %xmm6
	vpand	%xmm8, %xmm1, %xmm1
	vpackuswb	%xmm4, %xmm0, %xmm0
	vpackuswb	%xmm1, %xmm6, %xmm1
	vpmovzxbw	%xmm2, %xmm2
	vpmovzxbw	%xmm0, %xmm4
	vpsllw	$8, %xmm7, %xmm7
	vpmovzxbw	%xmm1, %xmm8
	vpmovzxwd	%xmm4, %xmm6
	vpsrldq	$8, %xmm4, %xmm4
	vpmovzxwd	%xmm7, %xmm9
	vpslld	$16, %xmm6, %xmm6
	vpsrldq	$8, %xmm7, %xmm7
	vpmovzxwd	%xmm4, %xmm4
	vpor	%xmm9, %xmm6, %xmm6
	vpmovzxwd	%xmm8, %xmm9
	vpmovzxwd	%xmm7, %xmm7
	vpslld	$16, %xmm4, %xmm4
	vpsrldq	$8, %xmm8, %xmm8
	vpor	%xmm9, %xmm6, %xmm6
	vpmovzxwd	%xmm5, %xmm9
	vpsrldq	$8, %xmm5, %xmm5
	vpor	%xmm7, %xmm4, %xmm4
	vpmovzxwd	%xmm8, %xmm8
	vpsrldq	$8, %xmm0, %xmm0
	vpmovzxwd	%xmm5, %xmm5
	vpslld	$24, %xmm5, %xmm5
	vpor	%xmm8, %xmm4, %xmm4
	vpmovzxbw	%xmm0, %xmm0
	vpsllw	$8, %xmm2, %xmm2
	vpsrldq	$8, %xmm1, %xmm1
	vpor	%xmm5, %xmm4, %xmm4
	vmovdqa	%xmm4, 80(%rsp)
	vpmovzxwd	%xmm0, %xmm4
	vpsrldq	$8, %xmm0, %xmm0
	vpmovzxwd	%xmm2, %xmm5
	vpmovzxbw	%xmm1, %xmm1
	vpslld	$16, %xmm4, %xmm4
	vpmovzxwd	%xmm0, %xmm0
	vpsrldq	$8, %xmm2, %xmm2
	vpsrldq	$8, %xmm3, %xmm3
	vpor	%xmm5, %xmm4, %xmm4
	vpmovzxwd	%xmm2, %xmm2
	vpmovzxwd	%xmm1, %xmm5
	vpmovzxbw	%xmm3, %xmm3
	vpslld	$16, %xmm0, %xmm0
	vpsrldq	$8, %xmm1, %xmm1
	vpor	%xmm5, %xmm4, %xmm4
	vpor	%xmm2, %xmm0, %xmm0
	vpmovzxwd	%xmm1, %xmm1
	vmovdqu	(%r11), %ymm2
	vpmovzxwd	%xmm3, %xmm5
	vpslld	$24, %xmm9, %xmm9
	vpslld	$24, %xmm5, %xmm5
	vpor	%xmm1, %xmm0, %xmm0
	vpsrldq	$8, %xmm3, %xmm1
	vpor	%xmm9, %xmm6, %xmm6
	vpor	%xmm5, %xmm4, %xmm4
	vpextrd	$3, %xmm2, 56(%rsp)
	vpmovzxwd	%xmm1, %xmm1
	movl	56(%rsp), %ebx
	vmovdqa	%xmm6, 64(%rsp)
	vpextrd	$2, %xmm2, %r8d
	vpslld	$24, %xmm1, %xmm1
	vmovdqa	%xmm4, 96(%rsp)
	vpextrd	$1, %xmm2, %r13d
	vpor	%xmm1, %xmm0, %xmm0
	vmovd	%xmm2, 60(%rsp)
	vmovdqa	%xmm0, 112(%rsp)
	vextracti128	$0x1, %ymm2, %xmm0
	vpextrd	$1, %xmm0, 44(%rsp)
	vmovd	%xmm0, %r10d
	vpextrd	$3, %xmm0, 36(%rsp)
	movl	%eax, 32(%rsp)
	movq	%r11, 16(%rsp)
	movl	60(%rsp), %r9d
	vpextrd	$2, %xmm0, %r14d
	movl	$1013904242, 28(%rsp)
	.p2align 4
	.p2align 3
.L2:
	movzbl	(%r15), %r11d
	movl	64(%rsp,%r11,4), %eax
	addl	%r10d, %eax
	leal	(%rax,%r9), %r11d
	movzbl	1(%r15), %r9d
	xorl	%r11d, %esi
	movl	64(%rsp,%r9,4), %eax
	rorx	$16, %esi, %esi
	addl	%esi, %edi
	xorl	%edi, %r10d
	rorx	$12, %r10d, %r10d
	addl	%r10d, %eax
	leal	(%rax,%r11), %r9d
	xorl	%r9d, %esi
	rorx	$8, %esi, %esi
	leal	(%rdi,%rsi), %eax
	movzbl	2(%r15), %edi
	movl	%esi, 60(%rsp)
	xorl	%eax, %r10d
	movl	%eax, 56(%rsp)
	movl	32(%rsp), %eax
	rorx	$7, %r10d, %r11d
	movl	%r11d, 24(%rsp)
	movl	44(%rsp), %r11d
	addl	64(%rsp,%rdi,4), %r11d
	movzbl	3(%r15), %r10d
	addl	%r13d, %r11d
	movl	44(%rsp), %edi
	xorl	%r11d, %eax
	movl	64(%rsp,%r10,4), %r13d
	rorx	$16, %eax, %eax
	addl	%eax, %edx
	xorl	%edx, %edi
	rorx	$12, %edi, %edi
	addl	%edi, %r13d
	leal	0(%r13,%r11), %r10d
	xorl	%r10d, %eax
	rorx	$8, %eax, %eax
	leal	(%rdx,%rax), %r13d
	movzbl	4(%r15), %edx
	xorl	%r13d, %edi
	movl	%r13d, 52(%rsp)
	movl	64(%rsp,%rdx,4), %r11d
	movl	28(%rsp), %edx
	rorx	$7, %edi, %edi
	addl	%r14d, %r11d
	addl	%r11d, %r8d
	movzbl	5(%r15), %r11d
	xorl	%r8d, %ecx
	rorx	$16, %ecx, %ecx
	leal	(%rdx,%rcx), %r13d
	xorl	%r13d, %r14d
	rorx	$12, %r14d, %edx
	movl	64(%rsp,%r11,4), %r14d
	addl	%edx, %r14d
	leal	(%r14,%r8), %r11d
	movl	36(%rsp), %r14d
	movl	40(%rsp), %r8d
	xorl	%r11d, %ecx
	rorx	$8, %ecx, %ecx
	addl	%ecx, %r13d
	movl	%ecx, 48(%rsp)
	movzbl	6(%r15), %ecx
	xorl	%r13d, %edx
	addl	64(%rsp,%rcx,4), %r14d
	movl	36(%rsp), %ecx
	rorx	$7, %edx, %edx
	addl	%ebx, %r14d
	movzbl	7(%r15), %ebx
	xorl	%r14d, %r8d
	movl	64(%rsp,%rbx,4), %esi
	rorx	$16, %r8d, %r8d
	addl	%r8d, %r12d
	xorl	%r12d, %ecx
	rorx	$12, %ecx, %ecx
	addl	%ecx, %esi
	leal	(%rsi,%r14), %ebx
	movzbl	8(%r15), %r14d
	xorl	%ebx, %r8d
	rorx	$8, %r8d, %r8d
	addl	%r8d, %r12d
	xorl	%r12d, %ecx
	addl	64(%rsp,%r14,4), %r9d
	movzbl	9(%r15), %r14d
	addl	%edi, %r9d
	rorx	$7, %ecx, %ecx
	xorl	%r9d, %r8d
	addl	64(%rsp,%r14,4), %r9d
	rorx	$16, %r8d, %r8d
	addl	%r8d, %r13d
	xorl	%r13d, %edi
	rorx	$12, %edi, %edi
	addl	%edi, %r9d
	xorl	%r9d, %r8d
	rorx	$8, %r8d, %esi
	movl	%esi, 40(%rsp)
	addl	%r13d, %esi
	xorl	%esi, %edi
	movl	%esi, 28(%rsp)
	movl	60(%rsp), %esi
	rorx	$7, %edi, %edi
	movl	%edi, 44(%rsp)
	movzbl	10(%r15), %edi
	addl	64(%rsp,%rdi,4), %r10d
	leal	(%r10,%rdx), %r13d
	xorl	%r13d, %esi
	rorx	$16, %esi, %esi
	addl	%esi, %r12d
	xorl	%r12d, %edx
	rorx	$12, %edx, %r14d
	movzbl	11(%r15), %edx
	addl	64(%rsp,%rdx,4), %r13d
	movzbl	12(%r15), %edx
	addl	%r14d, %r13d
	addl	64(%rsp,%rdx,4), %r11d
	movl	56(%rsp), %edx
	xorl	%r13d, %esi
	leal	(%r11,%rcx), %r8d
	movl	24(%rsp), %r11d
	rorx	$8, %esi, %esi
	addl	%esi, %r12d
	xorl	%r8d, %eax
	xorl	%r12d, %r14d
	rorx	$16, %eax, %eax
	leal	(%rdx,%rax), %edi
	movzbl	13(%r15), %edx
	movl	%r11d, %r10d
	xorl	%edi, %ecx
	rorx	$7, %r14d, %r14d
	addl	64(%rsp,%rdx,4), %r8d
	rorx	$12, %ecx, %ecx
	addl	%ecx, %r8d
	xorl	%r8d, %eax
	rorx	$8, %eax, %eax
	addl	%eax, %edi
	movl	%eax, 32(%rsp)
	movl	52(%rsp), %eax
	xorl	%edi, %ecx
	rorx	$7, %ecx, %edx
	movl	%edx, 36(%rsp)
	movzbl	14(%r15), %edx
	movl	48(%rsp), %ecx
	addl	64(%rsp,%rdx,4), %ebx
	addl	%r11d, %ebx
	movzbl	15(%r15), %r11d
	xorl	%ebx, %ecx
	rorx	$16, %ecx, %ecx
	leal	(%rax,%rcx), %edx
	addl	64(%rsp,%r11,4), %ebx
	leaq	160+SIGMA(%rip), %rax
	xorl	%edx, %r10d
	rorx	$12, %r10d, %r10d
	addl	%r10d, %ebx
	addq	$16, %r15
	xorl	%ebx, %ecx
	rorx	$8, %ecx, %ecx
	addl	%ecx, %edx
	xorl	%edx, %r10d
	rorx	$7, %r10d, %r10d
	cmpq	%rax, %r15
	jne	.L2
	movl	%r9d, %r15d
	movl	32(%rsp), %eax
	movl	%r13d, %r9d
	movl	28(%rsp), %r13d
	movl	%r15d, 128(%rsp)
	movl	40(%rsp), %r15d
	movl	%eax, 180(%rsp)
	movl	36(%rsp), %eax
	movl	%r15d, 188(%rsp)
	movl	44(%rsp), %r15d
	movl	%r13d, 168(%rsp)
	movq	16(%rsp), %r11
	movl	%r15d, 148(%rsp)
	movl	%r9d, 132(%rsp)
	movl	%esi, 176(%rsp)
	movl	%r12d, 172(%rsp)
	movl	%r14d, 152(%rsp)
	movl	%r8d, 136(%rsp)
	movl	%edi, 160(%rsp)
	movl	%eax, 156(%rsp)
	movl	%ebx, 140(%rsp)
	movl	%ecx, 184(%rsp)
	movl	%edx, 164(%rsp)
	movl	%r10d, 144(%rsp)
	vmovdqa	128(%rsp), %ymm0
	vpxor	160(%rsp), %ymm0, %ymm0
	vpxor	%ymm2, %ymm0, %ymm0
	vmovdqu	%ymm0, (%r11)
	movq	216(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L8
	vzeroupper
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L8:
	.cfi_restore_state
	vzeroupper
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE78:
	.size	compress, .-compress
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC1:
	.string	"toy prover: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB85:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC1(%rip), %rdx
	movl	$2, %esi
	xorl	%eax, %eax
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	%rdi, %rcx
	movq	stderr(%rip), %rdi
	call	__fprintf_chk@PLT
	movl	$1, %edi
	call	exit@PLT
	.cfi_endproc
.LFE85:
	.size	die, .-die
	.section	.rodata.str1.1
.LC2:
	.string	"out of memory"
	.text
	.p2align 4
	.type	app, @function
app:
.LFB86:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rdx, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	movq	8(%rdi), %rax
	movq	(%rdi), %rdi
	leaq	1(%rax,%rdx), %rbx
	movq	%rbx, %rsi
	call	realloc@PLT
	movq	%rax, 0(%rbp)
	testq	%rax, %rax
	je	.L14
	movq	8(%rbp), %rdx
	movq	%r13, %rsi
	cmpq	%rdx, %rbx
	leaq	(%rax,%rdx), %rdi
	cmovb	%rdx, %rbx
	movq	%rbx, %rcx
	subq	%rdx, %rcx
	movq	%r12, %rdx
	call	__memcpy_chk@PLT
	addq	%r12, 8(%rbp)
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L14:
	.cfi_restore_state
	leaq	.LC2(%rip), %rdi
	call	die
	.cfi_endproc
.LFE86:
	.size	app, .-app
	.section	.rodata.str1.1
.LC3:
	.string	"rb"
	.text
	.p2align 4
	.type	readfile, @function
readfile:
.LFB88:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	leaq	-65536(%rsp), %r11
	.cfi_def_cfa 11, 65584
.LPSRL0:
	subq	$4096, %rsp
	orq	$0, (%rsp)
	cmpq	%r11, %rsp
	jne	.LPSRL0
	.cfi_def_cfa_register 7
	subq	$32, %rsp
	.cfi_def_cfa_offset 65616
	leaq	.LC3(%rip), %rsi
	movq	%fs:40, %rbx
	movq	%rbx, 65560(%rsp)
	movq	%rdi, %rbx
	call	fopen@PLT
	testq	%rax, %rax
	je	.L21
	movq	%rax, %r13
	xorl	%ebx, %ebx
	xorl	%ebp, %ebp
	jmp	.L16
	.p2align 4,,10
	.p2align 3
.L17:
	movq	%rax, %rdx
	leaq	16(%rsp), %rsi
	movq	%rsp, %rdi
	movq	%rbp, (%rsp)
	movq	%rbx, 8(%rsp)
	call	app
	movq	(%rsp), %rbp
	movq	8(%rsp), %rbx
.L16:
	movq	%r13, %rcx
	movl	$65536, %edx
	movl	$1, %esi
	leaq	16(%rsp), %rdi
	call	fread@PLT
	testq	%rax, %rax
	jne	.L17
	movq	%r13, %rdi
	call	fclose@PLT
	movq	%rbp, %rax
	movq	%rbx, %rdx
	movq	65560(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L22
	addq	$65568, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L21:
	.cfi_restore_state
	movq	%rbx, %rdi
	call	die
.L22:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE88:
	.size	readfile, .-readfile
	.section	.rodata.str1.1
.LC4:
	.string	"%s.tmp"
.LC5:
	.string	"wb"
	.text
	.p2align 4
	.type	writefile, @function
writefile:
.LFB89:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	movq	%rdi, %r9
	movq	%rsi, %r14
	movl	$512, %ecx
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	movl	$512, %esi
	movq	%rdx, %r13
	leaq	.LC4(%rip), %r8
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	movl	$2, %edx
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	subq	$528, %rsp
	.cfi_def_cfa_offset 576
	movq	%fs:40, %rax
	movq	%rax, 520(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdi
	call	__snprintf_chk@PLT
	leaq	.LC5(%rip), %rsi
	movq	%rsp, %rdi
	call	fopen@PLT
	testq	%rax, %rax
	je	.L25
	movq	%rax, %rcx
	movq	%r13, %rdx
	movl	$1, %esi
	movq	%r14, %rdi
	movq	%rax, %rbp
	call	fwrite@PLT
	cmpq	%r13, %rax
	jne	.L25
	movq	%rbp, %rdi
	call	fclose@PLT
	testl	%eax, %eax
	jne	.L25
	movq	%r12, %rsi
	movq	%rsp, %rdi
	call	rename@PLT
	testl	%eax, %eax
	jne	.L25
	movq	520(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L32
	addq	$528, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L25:
	.cfi_restore_state
	movq	%r12, %rdi
	call	die
.L32:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE89:
	.size	writefile, .-writefile
	.p2align 4
	.type	blake2s, @function
blake2s:
.LFB79:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r14
	pushq	%r13
	.cfi_offset 14, -24
	.cfi_offset 13, -32
	movq	%rsi, %r13
	pushq	%r12
	.cfi_offset 12, -40
	movq	%rdi, %r12
	pushq	%rbx
	andq	$-32, %rsp
	addq	$-128, %rsp
	.cfi_offset 3, -48
	vmovdqa	.LC6(%rip), %ymm0
	movq	%fs:40, %r14
	movq	%r14, 120(%rsp)
	movq	%rdx, %r14
	vmovdqa	%ymm0, (%rsp)
	cmpq	$65, %rdx
	jne	.L59
	xorl	%ecx, %ecx
	movl	$64, %edx
	movq	%rsp, %rdi
	movq	%rsp, %rbx
	vzeroupper
	call	compress
	addq	$64, %r13
	movl	$1, %edx
.L44:
	vpxor	%xmm0, %xmm0, %xmm0
	leaq	48(%rsp), %rsi
	movl	%edx, %ecx
	movq	%r13, %rax
	vmovdqu	%ymm0, 48(%rsp)
	movq	%rsi, %rdi
	vmovdqu	%ymm0, 80(%rsp)
	cmpl	$8, %edx
	jnb	.L60
.L35:
	xorl	%edx, %edx
	testb	$4, %cl
	jne	.L61
	testb	$2, %cl
	jne	.L62
.L39:
	andl	$1, %ecx
	jne	.L63
.L40:
	movq	%rbx, %rdi
	movl	$1, %ecx
	movq	%r14, %rdx
	vzeroupper
	call	compress
	movq	%rbx, %r8
	xorl	%edi, %edi
	.p2align 4
	.p2align 3
.L41:
	movl	(%r8), %esi
	leaq	(%r12,%rdi), %rdx
	xorl	%eax, %eax
.L42:
	shrx	%eax, %esi, %ecx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$32, %eax
	jne	.L42
	addq	$4, %rdi
	addq	$4, %r8
	cmpq	$32, %rdi
	jne	.L41
	movq	120(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L64
	leaq	-32(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L63:
	.cfi_restore_state
	movzbl	(%rax,%rdx), %eax
	movb	%al, (%rdi,%rdx)
	jmp	.L40
.L62:
	movzwl	(%rax,%rdx), %r8d
	movw	%r8w, (%rdi,%rdx)
	addq	$2, %rdx
	andl	$1, %ecx
	je	.L40
	jmp	.L63
.L61:
	movl	(%rax), %edx
	movl	%edx, (%rdi)
	movl	$4, %edx
	testb	$2, %cl
	je	.L39
	jmp	.L62
.L60:
	andl	$-8, %edx
	xorl	%eax, %eax
.L36:
	movl	%eax, %edi
	addl	$8, %eax
	movq	0(%r13,%rdi), %r8
	movq	%r8, (%rsi,%rdi)
	cmpl	%edx, %eax
	jb	.L36
	leaq	(%rsi,%rax), %rdi
	addq	%r13, %rax
	jmp	.L35
.L59:
	movq	%r14, %rdx
	movq	%rsp, %rbx
	jmp	.L44
.L64:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE79:
	.size	blake2s, .-blake2s
	.section	.rodata.str1.1
.LC8:
	.string	"ready"
.LC9:
	.string	"go"
.LC10:
	.string	"no go"
	.text
	.p2align 4
	.type	handshake, @function
handshake:
.LFB99:
	.cfi_startproc
	subq	$88, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %rdi
	movq	%rdi, 72(%rsp)
	leaq	.LC8(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movq	%rsp, %rdi
	movl	$64, %esi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L66
	cmpw	$28519, (%rsp)
	je	.L77
.L66:
	leaq	.LC10(%rip), %rdi
	call	die
.L77:
	movq	72(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L78
	addq	$88, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L78:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE99:
	.size	handshake, .-handshake
	.section	.rodata.str1.1
.LC11:
	.string	"%2x"
	.text
	.p2align 4
	.type	unhex.constprop.0, @function
unhex.constprop.0:
.LFB104:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	subq	$24, %rsp
	.cfi_def_cfa_offset 64
	movq	%fs:40, %rbx
	movq	%rbx, 8(%rsp)
	movq	%rsi, %rbx
	leaq	64(%rbx), %r13
	.p2align 4
	.p2align 3
.L82:
	xorl	%eax, %eax
	leaq	4(%rsp), %rdx
	leaq	.LC11(%rip), %rsi
	movq	%rbx, %rdi
	call	__isoc23_sscanf@PLT
	cmpl	$1, %eax
	jne	.L86
	movl	4(%rsp), %eax
	addq	$2, %rbx
	addq	$1, %rbp
	movb	%al, -1(%rbp)
	cmpq	%r13, %rbx
	jne	.L82
	xorl	%eax, %eax
.L79:
	movq	8(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L87
	addq	$24, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L86:
	.cfi_restore_state
	movl	$-1, %eax
	jmp	.L79
.L87:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE104:
	.size	unhex.constprop.0, .-unhex.constprop.0
	.section	.rodata.str1.1
.LC12:
	.string	""
	.text
	.p2align 4
	.type	read_stmt, @function
read_stmt:
.LFB101:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	movq	%rdi, %r12
	movq	%rsi, %rdi
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$32, %rsp
	.cfi_def_cfa_offset 64
	movq	%fs:40, %rbp
	movq	%rbp, 24(%rsp)
	movq	%rsi, %rbp
	call	readfile
	movq	%rsp, %rdi
	leaq	.LC12(%rip), %rsi
	movq	%rdx, 8(%rsp)
	movl	$1, %edx
	movq	%rax, (%rsp)
	call	app
	cmpq	$64, 8(%rsp)
	jbe	.L90
	movq	(%rsp), %rbx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L90
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L94
	addq	$32, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	movq	%rbx, %rdi
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	jmp	free@PLT
.L90:
	.cfi_restore_state
	movq	%rbp, %rdi
	call	die
.L94:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE101:
	.size	read_stmt, .-read_stmt
	.section	.rodata.str1.1
.LC13:
	.string	"RF_ORACLE"
.LC14:
	.string	"RF_ORACLE unset"
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC15:
	.string	"cannot connect to the oracle service"
	.section	.rodata.str1.1
.LC16:
	.string	"SIGN write"
.LC17:
	.string	"SIGN read"
.LC18:
	.string	"SIGN refused"
	.text
	.p2align 4
	.type	signed_file, @function
signed_file:
.LFB97:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$4096, %rsp
	orq	$0, (%rsp)
	subq	$864, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%rdi, 24(%rsp)
	movl	svc(%rip), %edi
	movq	%fs:40, %r13
	movq	%r13, 4952(%rsp)
	movq	%rsi, %r13
	testl	%edi, %edi
	js	.L118
.L97:
	leaq	160(%rsp), %r12
	movl	$16, %edx
	movq	$2, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	%r12, %rsi
	call	write@PLT
	cmpq	$16, %rax
	jne	.L119
	xorl	%ebx, %ebx
	.p2align 4
	.p2align 3
.L101:
	movl	$16, %edx
	movl	svc(%rip), %edi
	leaq	(%r12,%rbx), %rsi
	subq	%rbx, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L106
	addq	%rax, %rbx
	cmpq	$15, %rbx
	jbe	.L101
	cmpb	$0, 160(%rsp)
	jne	.L103
	movq	%r12, %rdx
	leaq	152(%rsp), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L104:
	movzbl	15(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rsi
	jne	.L104
	cmpq	$4772, %rax
	jne	.L103
	xorl	%r14d, %r14d
	leaq	176(%rsp), %r15
	.p2align 4
	.p2align 3
.L105:
	movl	$4772, %edx
	movl	svc(%rip), %edi
	leaq	(%r15,%r14), %rsi
	subq	%r14, %rdx
	movq	%rdx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L106
	addq	%rax, %r14
	cmpq	$4771, %r14
	jbe	.L105
	movq	%r12, %rdx
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L107:
	shrx	%rax, %r13, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L107
	movl	$8, %edx
	movq	%r12, %rsi
	leaq	32(%rsp), %rdi
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	call	app
	movq	24(%rsp), %rsi
	movq	%r13, %rdx
	leaq	32(%rsp), %rdi
	call	app
	movl	$8, %edx
	movq	%r12, %rsi
	movq	$0, 160(%rsp)
	leaq	32(%rsp), %rdi
	call	app
	movl	176(%rsp), %esi
	movq	%r12, %rdx
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L108:
	shrx	%rax, %rsi, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L108
	movl	$8, %edx
	movq	%r12, %rsi
	leaq	32(%rsp), %rdi
	call	app
	movl	$4768, %edx
	leaq	32(%rsp), %rdi
	leaq	180(%rsp), %rsi
	call	app
	movq	32(%rsp), %rax
	movq	40(%rsp), %rdx
	movq	4952(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L120
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
	.p2align 4,,10
	.p2align 3
.L118:
	.cfi_restore_state
	leaq	.LC13(%rip), %rdi
	call	getenv@PLT
	testq	%rax, %rax
	je	.L121
	movl	$1, %edx
	vpxor	%xmm0, %xmm0, %xmm0
	leaq	50(%rsp), %rdi
	movq	%rax, %rsi
	movw	%dx, 48(%rsp)
	movl	$107, %edx
	vmovdqu	%ymm0, 114(%rsp)
	vmovdqu	%ymm0, 50(%rsp)
	vmovdqu	%ymm0, 82(%rsp)
	vmovdqu	%xmm0, 142(%rsp)
	vzeroupper
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, svc(%rip)
	testl	%eax, %eax
	js	.L100
	movl	$110, %edx
	leaq	48(%rsp), %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	jne	.L100
	movl	svc(%rip), %edi
	jmp	.L97
.L106:
	leaq	.LC17(%rip), %rdi
	call	die
.L119:
	leaq	.LC16(%rip), %rdi
	call	die
.L120:
	call	__stack_chk_fail@PLT
.L103:
	leaq	.LC18(%rip), %rdi
	call	die
.L121:
	leaq	.LC14(%rip), %rdi
	call	die
.L100:
	leaq	.LC15(%rip), %rdi
	call	die
	.cfi_endproc
.LFE97:
	.size	signed_file, .-signed_file
	.p2align 4
	.type	prove_leaf, @function
prove_leaf:
.LFB98:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%rsi, %rbx
	andq	$-32, %rsp
	subq	$160, %rsp
	vmovdqu	(%rdi), %ymm0
	movq	%fs:40, %r14
	movq	%r14, 152(%rsp)
	movq	%rdx, %r14
	leaq	96(%rsp), %r13
	vmovdqa	%ymm0, 64(%rsp)
	testq	%rsi, %rsi
	je	.L123
	xorl	%r12d, %r12d
	leaq	96(%rsp), %r13
	.p2align 4
	.p2align 3
.L124:
	movb	$67, 96(%rsp)
	movl	$33, %edx
	movq	%r13, %rsi
	leaq	32(%rsp), %rdi
	vmovdqu	%ymm0, 97(%rsp)
	vmovdqa	%ymm0, 32(%rsp)
	vzeroupper
	call	blake2s
	addq	$1, %r12
	vmovdqa	32(%rsp), %ymm0
	cmpq	%r12, %rbx
	jne	.L124
.L123:
	movb	$76, 96(%rsp)
	leaq	129(%rsp), %rdx
	xorl	%eax, %eax
	vmovdqu	%ymm0, 97(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L125:
	shrx	%rax, %rbx, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L125
	movl	$41, %edx
	movq	%r13, %rsi
	movq	%r14, %rdi
	vzeroupper
	call	blake2s
	movl	$8, %edx
	movq	%r13, %rsi
	movq	$0, 96(%rsp)
	movq	$0, 16(%rsp)
	leaq	16(%rsp), %rdi
	movq	$0, 24(%rsp)
	call	app
	movl	$32, %edx
	leaq	64(%rsp), %rsi
	leaq	16(%rsp), %rdi
	call	app
	movq	%r13, %rdx
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L126:
	shrx	%rax, %rbx, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L126
	movq	%r13, %rsi
	movl	$8, %edx
	leaq	16(%rsp), %rdi
	call	app
	movq	16(%rsp), %rbx
	movq	24(%rsp), %rdx
	movq	%rbx, %rdi
	movq	%rdx, %rsi
	call	signed_file
	movq	%rbx, %rdi
	movq	%rax, %r12
	movq	%rdx, %r13
	call	free@PLT
	movq	152(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L135
	leaq	-40(%rbp), %rsp
	movq	%r12, %rax
	movq	%r13, %rdx
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L135:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE98:
	.size	prove_leaf, .-prove_leaf
	.section	.rodata.str1.1
.LC19:
	.string	"malformed child file"
	.section	.rodata.str1.8
	.align 8
.LC20:
	.string	"trailing bytes in a child file"
	.text
	.p2align 4
	.type	app_signed_words, @function
app_signed_words:
.LFB95:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$96, %rsp
	.cfi_offset 15, -24
	.cfi_offset 14, -32
	.cfi_offset 13, -40
	.cfi_offset 12, -48
	.cfi_offset 3, -56
	movq	%fs:40, %rax
	movq	%rax, 88(%rsp)
	xorl	%eax, %eax
	cmpq	$7, %rdx
	jbe	.L139
	movq	%rdi, %rbx
	movq	%rsi, %r12
	movq	%rdx, %r13
	xorl	%r15d, %r15d
	leaq	7(%rsi), %rax
	leaq	-1(%rsi), %rcx
	.p2align 5
	.p2align 4
	.p2align 3
.L138:
	movzbl	(%rax), %edx
	salq	$8, %r15
	subq	$1, %rax
	orq	%rdx, %r15
	cmpq	%rcx, %rax
	jne	.L138
	leaq	-8(%r13), %r8
	cmpq	%r15, %r8
	jb	.L139
	leaq	64(%rsp), %rdx
	xorl	%eax, %eax
	movq	%rdx, 56(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L140:
	shrx	%rax, %r15, %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L140
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%r8, 48(%rsp)
	call	app
	movq	%r15, %rdx
	leaq	8(%r12), %rsi
	movq	%rbx, %rdi
	call	app
	movq	%r15, %rdx
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	negq	%rdx
	andl	$7, %edx
	call	app
	movq	48(%rsp), %r8
	subq	%r15, %r8
	cmpq	$7, %r8
	jbe	.L139
	leaq	-8(%r12), %rdi
	leaq	(%r15,%r12), %rax
	movq	$0, 32(%rsp)
	movq	%rdi, 24(%rsp)
	leaq	(%r15,%rdi), %rsi
	.p2align 5
	.p2align 4
	.p2align 3
.L141:
	movq	32(%rsp), %rdx
	movzbl	15(%rax), %ecx
	subq	$1, %rax
	salq	$8, %rdx
	orq	%rdx, %rcx
	movq	%rcx, 32(%rsp)
	cmpq	%rsi, %rax
	jne	.L141
	movq	56(%rsp), %rdx
	addq	$16, %r15
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L142:
	shrx	%rax, 32(%rsp), %rcx
	addl	$8, %eax
	movb	%cl, (%rdx)
	addq	$1, %rdx
	cmpl	$64, %eax
	jne	.L142
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	call	app
	cmpq	$0, 32(%rsp)
	je	.L143
	xorl	%r14d, %r14d
	.p2align 4
	.p2align 3
.L146:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$7, %rax
	jbe	.L139
	movq	24(%rsp), %rax
	leaq	(%r15,%r12), %rdx
	leaq	(%r15,%rax), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L144:
	movzbl	7(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rsi
	jne	.L144
	addq	$8, %r15
	movq	%r13, %rdx
	subq	%r15, %rdx
	cmpq	%rax, %rdx
	jb	.L139
	leaq	(%r12,%r15), %rdi
	movq	56(%rsp), %rcx
	xorl	%edx, %edx
	movq	%rdi, 48(%rsp)
	.p2align 5
	.p2align 4
	.p2align 3
.L145:
	shrx	%rdx, %rax, %rsi
	addl	$8, %edx
	movb	%sil, (%rcx)
	addq	$1, %rcx
	cmpl	$64, %edx
	jne	.L145
	movq	56(%rsp), %rsi
	movl	$8, %edx
	movq	%rbx, %rdi
	movq	%rax, 40(%rsp)
	call	app
	movq	40(%rsp), %rdx
	movq	48(%rsp), %rsi
	movq	%rbx, %rdi
	call	app
	movq	40(%rsp), %rax
	leaq	ZERO8(%rip), %rsi
	movq	%rbx, %rdi
	movq	%rax, %rdx
	movq	%rax, 48(%rsp)
	negq	%rdx
	andl	$7, %edx
	call	app
	addq	48(%rsp), %r15
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$31, %rax
	jbe	.L139
	leaq	(%r12,%r15), %rsi
	movl	$32, %edx
	movq	%rbx, %rdi
	addq	$32, %r15
	call	app
	addq	$1, %r14
	cmpq	32(%rsp), %r14
	jne	.L146
.L143:
	movq	%r13, %rax
	subq	%r15, %rax
	cmpq	$4775, %rax
	jbe	.L139
	leaq	(%r12,%r15), %rsi
	movl	$4776, %edx
	movq	%rbx, %rdi
	addq	$4776, %r15
	call	app
	cmpq	%r15, %r13
	jne	.L161
	movq	88(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L162
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L139:
	.cfi_restore_state
	leaq	.LC19(%rip), %rdi
	call	die
.L162:
	call	__stack_chk_fail@PLT
.L161:
	leaq	.LC20(%rip), %rdi
	call	die
	.cfi_endproc
.LFE95:
	.size	app_signed_words, .-app_signed_words
	.p2align 4
	.type	ws_node, @function
ws_node:
.LFB96:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r15
	.cfi_offset 15, -24
	movq	%rdi, %r15
	pushq	%r14
	.cfi_offset 14, -32
	movq	%rsi, %r14
	pushq	%r13
	.cfi_offset 13, -40
	movq	%rdx, %r13
	movl	$8, %edx
	pushq	%r12
	.cfi_offset 12, -48
	movq	%rcx, %r12
	pushq	%rbx
	andq	$-32, %rsp
	subq	$64, %rsp
	.cfi_offset 3, -56
	movq	%r8, (%rsp)
	leaq	32(%rsp), %rsi
	leaq	16(%rsp), %rdi
	movq	%r9, 8(%rsp)
	movq	%fs:40, %rax
	movq	%rax, 56(%rsp)
	xorl	%eax, %eax
	movq	$1, 32(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	call	app
	movl	$32, %edx
	movq	%r15, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movl	$32, %edx
	movq	%r14, %rsi
	leaq	16(%rsp), %rdi
	call	app
	movq	%r13, %rsi
	movq	%r12, %rdx
	leaq	16(%rsp), %rdi
	call	app_signed_words
	movq	8(%rsp), %rdx
	movq	(%rsp), %rsi
	leaq	16(%rsp), %rdi
	call	app_signed_words
	movq	16(%rsp), %rax
	movq	24(%rsp), %rdx
	movq	56(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L166
	leaq	-40(%rbp), %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L166:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE96:
	.size	ws_node, .-ws_node
	.section	.rodata.str1.8
	.align 8
.LC22:
	.string	"usage: prover setup|tree|leaf|node DIR"
	.section	.rodata.str1.1
.LC23:
	.string	"cannot enter DIR"
.LC24:
	.string	"setup"
.LC25:
	.string	"tree"
.LC26:
	.string	"leaves.json"
.LC27:
	.string	"\"n\":"
.LC28:
	.string	"leaves.json: n"
.LC29:
	.string	"\"starts\":"
.LC30:
	.string	"leaves.json: starts"
.LC31:
	.string	"leaves.json: start length"
.LC32:
	.string	"leaves.json: start"
.LC33:
	.string	"proofs"
.LC34:
	.string	"proofs/L%zu.bin"
.LC35:
	.string	"proofs/N%d_%zu.bin"
.LC36:
	.string	"root.bin"
.LC37:
	.string	"leaf"
.LC38:
	.string	"leaf.json"
.LC39:
	.string	"\"start\":"
.LC40:
	.string	"leaf.json: start"
.LC41:
	.string	"proof.bin"
.LC42:
	.string	"done"
.LC43:
	.string	"node"
.LC44:
	.string	"child1.stmt"
.LC45:
	.string	"child2.stmt"
.LC46:
	.string	"child1.bin"
.LC47:
	.string	"child2.bin"
.LC48:
	.string	"unknown mode"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB102:
	.cfi_startproc
	endbr64
	leaq	8(%rsp), %r10
	.cfi_def_cfa 10, 0
	andq	$-32, %rsp
	pushq	-8(%r10)
	pushq	%rbp
	movq	%rsp, %rbp
	.cfi_escape 0x10,0x6,0x2,0x76,0
	pushq	%r15
	pushq	%r14
	pushq	%r13
	pushq	%r12
	pushq	%r10
	.cfi_escape 0xf,0x3,0x76,0x58,0x6
	.cfi_escape 0x10,0xf,0x2,0x76,0x78
	.cfi_escape 0x10,0xe,0x2,0x76,0x70
	.cfi_escape 0x10,0xd,0x2,0x76,0x68
	.cfi_escape 0x10,0xc,0x2,0x76,0x60
	pushq	%rbx
	subq	$320, %rsp
	.cfi_escape 0x10,0x3,0x2,0x76,0x50
	movq	%fs:40, %rax
	movq	%rax, -56(%rbp)
	xorl	%eax, %eax
	cmpl	$3, %edi
	jne	.L214
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L215
	movq	8(%rbx), %rbx
	leaq	.LC24(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L170
	leaq	.LC25(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L216
	leaq	.LC37(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L217
	leaq	.LC43(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L191
	call	handshake
	leaq	.LC44(%rip), %rsi
	leaq	-192(%rbp), %rdi
	call	read_stmt
	leaq	.LC45(%rip), %rsi
	leaq	-128(%rbp), %rdi
	call	read_stmt
	leaq	.LC46(%rip), %rdi
	call	readfile
	leaq	.LC47(%rip), %rdi
	movq	%rax, %r12
	movq	%rdx, %r13
	call	readfile
	leaq	-128(%rbp), %rsi
	leaq	-192(%rbp), %rdi
	movq	%r13, %rcx
	movq	%rdx, %r9
	movq	%rax, %r8
	movq	%r12, %rdx
	call	ws_node
	movq	%rax, %rdi
	movq	%rdx, %rsi
	call	signed_file
.L213:
	movq	%rax, %rsi
	leaq	.LC41(%rip), %rdi
	call	writefile
	leaq	.LC42(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
.L170:
	movq	-56(%rbp), %rax
	subq	%fs:40, %rax
	jne	.L218
	leaq	-48(%rbp), %rsp
	xorl	%eax, %eax
	popq	%rbx
	popq	%r10
	.cfi_remember_state
	.cfi_def_cfa 10, 0
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	leaq	-8(%r10), %rsp
	.cfi_def_cfa 7, 8
	ret
.L217:
	.cfi_restore_state
	call	handshake
	leaq	.LC38(%rip), %rdi
	call	readfile
	leaq	-240(%rbp), %rdi
	leaq	.LC12(%rip), %rsi
	movq	%rdx, -232(%rbp)
	movl	$1, %edx
	movq	%rax, -240(%rbp)
	call	app
	movq	-240(%rbp), %rdi
	leaq	.LC27(%rip), %rsi
	call	strstr@PLT
	movq	-240(%rbp), %rdi
	leaq	.LC39(%rip), %rsi
	movq	%rax, %rbx
	call	strstr@PLT
	testq	%rbx, %rbx
	je	.L195
	testq	%rax, %rax
	je	.L195
	leaq	8(%rax), %rdi
	movl	$34, %esi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L190
	leaq	1(%rax), %rsi
	leaq	-192(%rbp), %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L190
	leaq	4(%rbx), %rdi
	xorl	%esi, %esi
	movl	$10, %edx
	call	__isoc23_strtoull@PLT
	leaq	-128(%rbp), %rdx
	leaq	-192(%rbp), %rdi
	movq	%rax, %rsi
	call	prove_leaf
	jmp	.L213
.L216:
	leaq	.LC26(%rip), %rdi
	call	readfile
	leaq	-240(%rbp), %rdi
	leaq	.LC12(%rip), %rsi
	movq	%rdx, -232(%rbp)
	movl	$1, %edx
	movq	%rax, -240(%rbp)
	call	app
	movq	-240(%rbp), %rbx
	leaq	.LC27(%rip), %rsi
	movq	%rbx, %rdi
	call	strstr@PLT
	testq	%rax, %rax
	je	.L219
	leaq	4(%rax), %rdi
	movl	$10, %edx
	xorl	%esi, %esi
	call	__isoc23_strtoull@PLT
	movq	%rbx, %rdi
	leaq	.LC29(%rip), %rsi
	movq	%rax, -320(%rbp)
	call	strstr@PLT
	movq	%rax, %rbx
	testq	%rax, %rax
	je	.L220
	movl	$512, %edi
	call	malloc@PLT
	leaq	9(%rbx), %rdi
	movl	$34, %esi
	movq	%rax, -280(%rbp)
	call	strchr@PLT
	movq	%rax, %r15
	testq	%rax, %rax
	je	.L174
	movq	$16, -288(%rbp)
	xorl	%ecx, %ecx
	movq	%rcx, -264(%rbp)
	.p2align 4
	.p2align 3
.L180:
	movq	%r15, %rdi
	call	strlen@PLT
	cmpq	$65, %rax
	jbe	.L175
	cmpb	$34, 65(%r15)
	jne	.L175
	movq	-288(%rbp), %rsi
	cmpq	%rsi, -264(%rbp)
	je	.L221
.L177:
	movq	-264(%rbp), %rax
	movq	-280(%rbp), %rbx
	leaq	1(%r15), %r13
	leaq	65(%r15), %r12
	salq	$5, %rax
	movq	%rbx, -304(%rbp)
	movq	%rax, -296(%rbp)
	leaq	(%rbx,%rax), %r14
	.p2align 4
	.p2align 3
.L179:
	leaq	-244(%rbp), %rdx
	leaq	.LC11(%rip), %rsi
	movq	%r13, %rdi
	xorl	%eax, %eax
	call	__isoc23_sscanf@PLT
	movl	%eax, %r9d
	cmpl	$1, %eax
	jne	.L222
	movl	-244(%rbp), %eax
	addq	$2, %r13
	addq	$1, %r14
	movb	%al, -1(%r14)
	cmpq	%r12, %r13
	jne	.L179
	leaq	66(%r15), %rdi
	movq	-264(%rbp), %r13
	movl	$34, %esi
	movl	%r9d, -272(%rbp)
	call	strchr@PLT
	movl	-272(%rbp), %r9d
	addq	$1, %r13
	testq	%rax, %rax
	movq	%rax, %r15
	je	.L223
	movq	%r13, -264(%rbp)
	jmp	.L180
	.p2align 4,,10
	.p2align 3
.L222:
	leaq	.LC32(%rip), %rdi
	call	die
	.p2align 4,,10
	.p2align 3
.L221:
	movq	-264(%rbp), %rbx
	movq	-280(%rbp), %rdi
	movq	%rbx, %rsi
	salq	$6, %rsi
	call	realloc@PLT
	movq	%rax, -280(%rbp)
	leaq	(%rbx,%rbx), %rax
	movq	%rax, -288(%rbp)
	jmp	.L177
.L223:
	movl	$493, %esi
	leaq	.LC33(%rip), %rdi
	movl	%r9d, -264(%rbp)
	movq	%r13, -272(%rbp)
	call	mkdir@PLT
	movq	-296(%rbp), %rax
	addq	$32, %rax
	movq	%rax, %rdi
	movq	%rax, -328(%rbp)
	call	malloc@PLT
	movq	%r13, %rdi
	salq	$4, %rdi
	movq	%rax, %r15
	call	malloc@PLT
	movq	%rax, -312(%rbp)
	testq	%r13, %r13
	je	.L192
	movl	-264(%rbp), %r9d
	movq	%rax, %r12
	leaq	-192(%rbp), %rax
	movq	-304(%rbp), %r14
	movq	%rax, -280(%rbp)
	xorl	%ebx, %ebx
	movl	%r9d, -288(%rbp)
	movq	%r13, -264(%rbp)
	movq	%r15, %r13
	movq	%r15, -296(%rbp)
	movq	%rax, %r15
	.p2align 4
	.p2align 3
.L182:
	movq	-320(%rbp), %rsi
	movq	%r14, %rdi
	movq	%r13, %rdx
	addq	$16, %r12
	addq	$32, %r14
	addq	$32, %r13
	call	prove_leaf
	movq	%rbx, %r9
	movl	$64, %ecx
	movq	%r15, %rdi
	movq	%rax, -16(%r12)
	movl	$64, %esi
	xorl	%eax, %eax
	addq	$1, %rbx
	movq	%rdx, -8(%r12)
	leaq	.LC34(%rip), %r8
	movl	$2, %edx
	call	__snprintf_chk@PLT
	movq	-16(%r12), %rsi
	movq	-8(%r12), %rdx
	movq	%r15, %rdi
	call	writefile
	cmpq	%rbx, -264(%rbp)
	jne	.L182
	leaq	-128(%rbp), %rax
	cmpq	$1, -264(%rbp)
	movq	-272(%rbp), %r8
	movq	%rax, -336(%rbp)
	leaq	-224(%rbp), %rax
	movl	-288(%rbp), %r9d
	movq	%rax, -272(%rbp)
	movq	-296(%rbp), %r15
	je	.L192
	movl	%r9d, -320(%rbp)
	movq	%r15, -344(%rbp)
	.p2align 4
	.p2align 3
.L183:
	shrq	%r8
	movq	-344(%rbp), %r12
	movq	-312(%rbp), %r14
	xorl	%ebx, %ebx
	movq	%r8, -304(%rbp)
	movq	%r12, %r13
	.p2align 4
	.p2align 3
.L185:
	vmovdqu	(%r12), %ymm0
	movb	$78, -128(%rbp)
	movl	$65, %edx
	movq	-336(%rbp), %rsi
	movq	-272(%rbp), %rdi
	vmovdqu	%ymm0, -127(%rbp)
	vmovdqu	32(%r12), %ymm0
	vmovdqu	%ymm0, -95(%rbp)
	vzeroupper
	call	blake2s
	movq	16(%r14), %r8
	movq	24(%r14), %r9
	movq	8(%r14), %rcx
	movq	(%r14), %rdx
	movq	%rbx, %r11
	leaq	32(%r12), %rsi
	salq	$5, %r11
	movq	%r12, %rdi
	movq	%r11, -296(%rbp)
	call	ws_node
	movq	%rdx, %rsi
	movq	%rax, %rdi
	movq	%rax, -288(%rbp)
	call	signed_file
	movq	-288(%rbp), %rdi
	movq	%rdx, %r15
	movq	%rax, -264(%rbp)
	call	free@PLT
	movq	(%r14), %rdi
	call	free@PLT
	movq	16(%r14), %rdi
	call	free@PLT
	movq	-296(%rbp), %r11
	movq	%r13, %rdi
	movl	$32, %edx
	movq	-328(%rbp), %rcx
	movq	-272(%rbp), %rsi
	cmpq	%r11, %rcx
	cmovb	%r11, %rcx
	addq	$64, %r12
	addq	$32, %r14
	addq	$32, %r13
	subq	%r11, %rcx
	call	__memcpy_chk@PLT
	movq	-312(%rbp), %rcx
	movq	%rbx, %rax
	subq	$8, %rsp
	movq	-264(%rbp), %rdx
	salq	$4, %rax
	movl	-320(%rbp), %r9d
	leaq	.LC35(%rip), %r8
	movq	%r15, 8(%rcx,%rax)
	movq	-280(%rbp), %rdi
	movl	$64, %esi
	movq	%rdx, (%rcx,%rax)
	movl	$64, %ecx
	movl	$2, %edx
	xorl	%eax, %eax
	pushq	%rbx
	addq	$1, %rbx
	call	__snprintf_chk@PLT
	movq	-264(%rbp), %rsi
	movq	-280(%rbp), %rdi
	movq	%r15, %rdx
	call	writefile
	popq	%rax
	popq	%rdx
	cmpq	%rbx, -304(%rbp)
	jne	.L185
	movq	-304(%rbp), %r8
	addl	$1, -320(%rbp)
	cmpq	$1, %r8
	jne	.L183
.L192:
	movq	-312(%rbp), %rax
	leaq	.LC36(%rip), %rdi
	movq	(%rax), %rsi
	movq	8(%rax), %rdx
	call	writefile
	jmp	.L170
.L174:
	movl	$493, %esi
	leaq	.LC33(%rip), %rdi
	call	mkdir@PLT
	xorl	%edi, %edi
	call	malloc@PLT
	movq	%rax, -312(%rbp)
	jmp	.L192
.L175:
	leaq	.LC31(%rip), %rdi
	call	die
.L220:
	leaq	.LC30(%rip), %rdi
	call	die
.L191:
	leaq	.LC48(%rip), %rdi
	call	die
.L218:
	call	__stack_chk_fail@PLT
.L215:
	leaq	.LC23(%rip), %rdi
	call	die
.L219:
	leaq	.LC28(%rip), %rdi
	call	die
.L190:
	leaq	.LC40(%rip), %rdi
	call	die
.L195:
	leaq	.LC38(%rip), %rdi
	call	die
.L214:
	leaq	.LC22(%rip), %rdi
	call	die
	.cfi_endproc
.LFE102:
	.size	main, .-main
	.section	.rodata
	.align 8
	.type	ZERO8, @object
	.size	ZERO8, 8
ZERO8:
	.zero	8
	.data
	.align 4
	.type	svc, @object
	.size	svc, 4
svc:
	.long	-1
	.section	.rodata
	.align 32
	.type	SIGMA, @object
	.size	SIGMA, 160
SIGMA:
	.byte	0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	.byte	14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3
	.string	"\013\b\f"
	.byte	5,2,15,13,10,14,3,6,7,1,9,4
	.byte	7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8
	.string	"\t"
	.byte	5,7,2,4,10,15,14,1,11,12,6,8,3,13
	.byte	2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9
	.byte	12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11
	.byte	13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10
	.byte	6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5
	.byte	10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0
	.section	.rodata.cst32,"aM",@progbits,32
	.align 32
.LC6:
	.long	1795745351
	.long	-1150833019
	.long	1013904242
	.long	-1521486534
	.long	1359893119
	.long	-1694144372
	.long	528734635
	.long	1541459225
	.ident	"GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
